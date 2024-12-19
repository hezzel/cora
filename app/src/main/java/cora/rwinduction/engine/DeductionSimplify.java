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

package cora.rwinduction.engine;

import java.util.Set;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;

/** The deduction command for simplifying an equation with a Rule */
public final class DeductionSimplify extends DeductionRule {
  /**
   * Create a deduction rule that will manipulate the given partial proof, and print its output to
   * the given output module.
   */
  public DeductionSimplify(PartialProof proof, OutputModule module) {
    super(proof, module);
  }

  /**
   * Create a deduction rule that will manipulate the given partial proof, and not print any
   * output.
   */
  public DeductionSimplify(PartialProof proof) {
    super(proof);
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
   * domain.
   *
   * Note: to apply the rule l → r | φ with given substitution γ, we:
   * - determine the top Equation in the current proof state, and the indicated subterm:
   *   let's say C[s]_p ≈ t | ψ
   * - determine an extension δ of γ so that lδ = s (if any)
   * - check that all (meta-)vars in the rule are in dom(δ), and if not, either extend it or fail
   * - check that ψ ⇒ φδ is valid
   * - replaces the equation by C[rδ]_p ≈ t | ψ
   *
   * The given ruleRenaming is only used for error messages, if any are needed.
   */
  public boolean apply(String ruleName, EquationPosition pos, Substitution subst) {
    // get the information of the given rule
    Rule rule = _proof.getRule(ruleName);
    Renaming ruleNaming = _proof.getRenaming(ruleName);
    // determine the top Equation in the current proof state, and the indicated subterm
    Equation eq = _proof.getProofState().getTopEquation();
    Term subterm = eq.querySubterm(pos);
    if (subterm == null) { println("No such position: %a.", pos); return false; }
    // determine an extension δ of γ so that lδ = s (if any)
    Substitution delta = subst.copy();
    String problem = rule.queryLeftSide().match(subterm, delta);
    if (problem != null) { println("The rule does not apply: %a", problem); return false; }
    // check that all (meta-)vars in the rule are in dom(δ), and if not, either extend it or fail
    if (!checkEverythingSubstituted(rule, ruleNaming, delta)) return false;
    // check that the constraint is implied by the equation's constraint
    if (!checkConstraintVariables(rule, ruleNaming, eq, delta)) return false;
    if (!checkImplication(rule, ruleNaming, eq, delta)) return false;
    // replace the equation!
    Term substituted = rule.queryRightSide().substitute(delta);
    Equation replaced = eq.replaceSubterm(pos, substituted);
    ProofState state = _proof.getProofState().replaceTopEquation(replaced);
    _proof.addProofStep(state, generateCommandSyntax(ruleName, pos, subst, eq.getRenaming()));
    return true;
  }

  /**
   * This function goes over all meta-variables in rule, and ensures that they're all in the
   * domain of delta.  If not, we either return false and print a failure message to the user, or
   * adapt the substitution to ensure the property.
   */
  private boolean checkEverythingSubstituted(Rule rule, Renaming naming, Substitution delta) {
    Set<Replaceable> missing = new TreeSet<Replaceable>();
    for (Replaceable x : rule.queryRightSide().freeReplaceables()) {
      if (delta.get(x) == null) missing.add(x);
    }
    for (Replaceable x : rule.queryConstraint().freeReplaceables()) {
      if (delta.get(x) == null) missing.add(x);
    }
    if (missing.isEmpty()) return true;
    StringBuilder builder = new StringBuilder();
    boolean first = true;
    for (Replaceable x : missing) {
      if (first) first = false; 
      else builder.append(", ");
      builder.append(naming.getName(x));
    }
    println("Not enough information given: I could not determine the substitution to be used " +
      "for %a.", builder.toString());
    return false;
  }

  /**
   * This function goes over all the variables in the constraint of rule, and verifies that they
   * are all mapped either to values by the substitution, or to variables in the constraint of the
   * equation.  The rule naming is used to print an error if this is not the case.
   */
  private boolean checkConstraintVariables(Rule rule, Renaming ruleNaming, Equation equation,
                                           Substitution delta) {
    Term constraint = equation.getConstraint();
    for (Variable x : rule.queryConstraint().vars()) {
      Term t = delta.getReplacement(x);
      if (t.isValue()) continue;
      if (!t.isVariable() || !constraint.freeReplaceables().contains(t.queryVariable())) {
        println("The rule does not apply: constraint variable %a is instantiated by %a, " +
          "which is not a value, nor a variable in the constraint of the equation.",
          ruleNaming.getName(x), new Pair<Term,Renaming>(t, equation.getRenaming()));
        return false;
      }
    }
    return true;
  }

  /**
   * For a rule l → r | φ, substitution δt and equation s ≈ t | ψ, this checks if ψ ⇒ φδ is valid.
   */
  private boolean checkImplication(Rule rule, Renaming naming, Equation equation,
                                   Substitution delta) {
    if (!rule.isConstrained()) return true; // no implication to prove if the rule is unconstrained
    Term psi = equation.getConstraint();
    Term phidelta = rule.queryConstraint().substitute(delta);
    Renaming renaming = equation.getRenaming();
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(psi, phidelta);
    if (Settings.smtSolver.checkValidity(translator.queryProblem())) return true;
    println("The rule does not apply: I could not prove that %a %{Vdash} %a.",
      new Pair<Term,Renaming>(psi, renaming), new Pair<Term,Renaming>(phidelta, renaming));
    return false;
  }

  private String generateCommandSyntax(String ruleName, EquationPosition pos, Substitution subst,
                                       Renaming equationNaming) {
    Renaming ruleNaming = _proof.getRenaming(ruleName);
    TermPrinter termPrinter = _module.queryTermPrinter();
    StringBuilder ret = new StringBuilder("simplify ");
    ret.append(ruleName + " ");
    ret.append(pos.toString());
    // go through the domain in the right order
    Set<Replaceable> domain = new TreeSet<Replaceable>(subst.domain());
    if (domain.isEmpty()) return ret.toString();
    boolean first = true;
    ret.append(" with [");
    for (Replaceable x : domain) {
      if (first) first = false;
      else ret.append("; ");
      ret.append(ruleNaming.getName(x));
      ret.append(" := ");
      termPrinter.print(subst.get(x), equationNaming, ret);
    }
    ret.append("]");
    return ret.toString();
  }
}

