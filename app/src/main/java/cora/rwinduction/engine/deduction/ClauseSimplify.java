/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine.deduction;

import java.util.Set;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.io.ParseableTermPrinter;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.StepSimplify;

/** The deduction command for simplifying an equation with a Rule */
public final class ClauseSimplify extends DeductionRule {
  /**
   * Create a deduction rule that will manipulate the given partial proof, and print its output to
   * the given output module.
   */
  public ClauseSimplify(PartialProof proof, OutputModule module) {
    super(proof, module);
  }

  /**
   * Create a deduction rule that will manipulate the given partial proof, and not print any
   * output.
   */
  public ClauseSimplify(PartialProof proof) {
    super(proof);
  }

  /**
   * This determines the missing information needed to create a deduction step -- which includes
   * the full substitution obtained by matching, since the user may be giving us a partial one --
   * and returns the result (or null if the rule is clearly not applicable at that position with
   * the given partial substitution).
   */
  StepSimplify createStep(String ruleName, EquationPosition pos, Substitution subst) {
    // determine the top Equation in the current proof state, and the subterm indicated by pos
    Rule rule = _proof.getRule(ruleName);
    Renaming ruleNaming = _proof.getRenaming(ruleName);
    Equation eq = _proof.getProofState().getTopEquation();
    Term s = eq.querySubterm(pos);
    if (s == null) { println("No such position: %a.", pos); return null; }
    // writing C[s]_p ≈ t | ψ for eq, determine an extension δ of γ so that lδ = s (if any)
    Substitution delta = subst.copy();
    String problem = rule.queryLeftSide().match(s, delta);
    if (problem != null) { println("The rule does not apply: %a", problem); return null; }
    return new StepSimplify(eq, rule, pos, delta, ruleName, ruleNaming);
  }

  /**
   * This function checks if we can indeed apply the rule l → r | φ with the substitution γ to the
   * equation C[lγ]_p ≈ t | ψ, with data as given by step.  Note that, for a step to be created, it
   * is already given that l γ is indeed the subterm at the given position of the equation.  Hence,
   * the remaining checks are:
   * - check that all (meta-)vars in the rule are in dom(δ)
   * - check that ψ ⇒ φδ is valid
   */
  private boolean verifyCorrectApplication(StepSimplify step) {
    if (!checkEverythingSubstituted(step)) return false;
    if (!checkConstraintVariables(step)) return false;
    if (!checkImplication(step)) return false;
    return true;
  }

  /**
   * Simplify the top equation by the given rule at the given position.
   * No default substitution is given, so if the rule has fresh variables in the right-hand side or
   * constraint, the command will have to guess them, or fails.
   */
  public boolean apply(String ruleName, EquationPosition pos) {
    return apply(ruleName, pos, TermFactory.createEmptySubstitution());
  }

  /**
   * Simplify the top equation by the given rule at the given position.  The substitution used for
   * the reduction should correspond to the given substitution on the variables in the latter's
   * domain, and have a mapping for all variables in the rule's constraint (although the clause may
   * guess them if this is not the case).
   */
  public boolean apply(String ruleName, EquationPosition pos, Substitution subst) {
    StepSimplify step = createStep(ruleName, pos, subst);
    if (step == null) return false;
    if (!verifyCorrectApplication(step)) return false;
    return applyStep(step);
  }

  /**
   * This function goes over all meta-variables in the step's rule, and ensures that they're all in
   * the domain of the step's substitution.  If not, we return false and print a failure message to
   * the user.
   *
   * Since it is already guaranteed that the left-hand side is fully mapped, we only consider the
   * replaceables in the right-hand side and constraint.
   */
  private boolean checkEverythingSubstituted(StepSimplify step) {
    Rule rule = step.getRule();
    Substitution subst = step.getSubstitution();
    Set<Replaceable> missing = new TreeSet<Replaceable>();
    for (Replaceable x : rule.queryRightSide().freeReplaceables()) {
      if (subst.get(x) == null) missing.add(x);
    }
    for (Replaceable x : rule.queryConstraint().freeReplaceables()) {
      if (subst.get(x) == null) missing.add(x);
    }
    if (missing.isEmpty()) return true;
    StringBuilder builder = new StringBuilder();
    boolean first = true;
    for (Replaceable x : missing) {
      if (first) first = false; 
      else builder.append(", ");
      builder.append(step.getRuleRenaming().getName(x));
    }
    println("Not enough information given: I could not determine the substitution to be used " +
      "for %a.", builder.toString());
    return false;
  }

  /**
   * This function goes over all the variables in the constraint of the rule, and verifies that they
   * are all mapped either to values by the substitution, or to variables in the constraint of the
   * equation.  The rule naming is used to print an error if this is not the case.
   */
  private boolean checkConstraintVariables(StepSimplify step) {
    Equation equation = step.getEquation();
    Term constraint = equation.getConstraint();
    for (Variable x : step.getRule().queryConstraint().vars()) {
      Term t = step.getSubstitution().getReplacement(x);
      if (t.isValue()) continue;
      if (!t.isVariable() || !constraint.freeReplaceables().contains(t.queryVariable())) {
        println("The rule does not apply: constraint variable %a is instantiated by %a, " +
          "which is not a value, nor a variable in the constraint of the equation.",
          step.getRuleRenaming().getName(x), new Pair<Term,Renaming>(t, equation.getRenaming()));
        return false;
      }
    }
    return true;
  }

  /**
   * For a rule l → r | φ, substitution δt and equation s ≈ t | ψ, this checks if ψ ⇒ φδ is valid.
   */
  private boolean checkImplication(StepSimplify step) {
    Rule rule = step.getRule();
    Equation equation = step.getEquation();
    if (!rule.isConstrained()) return true; // no implication to prove if the rule is unconstrained
    Term psi = equation.getConstraint();
    Term phidelta = rule.queryConstraint().substitute(step.getSubstitution());
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(psi, phidelta);
    if (Settings.smtSolver.checkValidity(translator.queryProblem())) return true;
    Renaming renaming = equation.getRenaming();
    println("The rule does not apply: I could not prove that %a %{Vdash} %a.",
      new Pair<Term,Renaming>(psi, renaming), new Pair<Term,Renaming>(phidelta, renaming));
    return false;
  }
}

