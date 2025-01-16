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

import java.util.Optional;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** The deduction command for simplifying an equation with a Rule */
public final class DeductionSimplify extends DeductionStep {
  private Rule _rule;
  private EquationPosition _position;
  private Substitution _substitution;
  private String _ruleName;
  private Renaming _ruleRenaming;

  private DeductionSimplify(ProofState state, ProofContext context, String ruleName,
                            EquationPosition position, Substitution substitution) {
    super(state, context);
    _ruleName = ruleName;
    _rule = context.getRule(ruleName);
    _ruleRenaming = context.getRenaming(ruleName);
    _position = position;
    _substitution = substitution;
  }

  /**
   * Creates a simplification check for the given information, checking that there is indeed a
   * match but NOT that the constraint is satisfied or that no new variables are created.
   * The substitution will not be altered, and does not become the property of the step; it is
   * safe to change afterwards.
   */
  public static Optional<DeductionSimplify> createStep(PartialProof proof, Optional<OutputModule> m,
                                                       String ruleName, EquationPosition pos,
                                                       Substitution subst) {
    // determine the top Equation in the current proof state, and the subterm indicated by pos
    Equation eq = getTopEquation(proof.getProofState(), m);
    if (eq == null);
    Term s = eq.querySubterm(pos);
    if (s == null) {
      m.ifPresent(o -> o.println("No such position: %a.", pos));
      return Optional.empty();
    }
    
    // determine the data on the rule
    Rule rule = proof.getContext().getRule(ruleName);
    if (rule == null) {
      m.ifPresent(o -> o.println("No such rule: %a.", ruleName));
      return Optional.empty();
    }

    // writing C[s]_p ≈ t | ψ for eq, determine an extension δ of γ so that lδ = s (if any)
    Substitution delta = subst.copy();
    String problem = rule.queryLeftSide().match(s, delta);
    if (problem != null) {
      m.ifPresent(o -> o.println("The rule does not apply: %a", problem));
      return Optional.empty();
    }
    
    // build step
    return Optional.of(new DeductionSimplify(proof.getProofState(), proof.getContext(),
                                             ruleName, pos, delta));
  }

  /**
   * This function checks if we can indeed apply the rule l → r | φ with the substitution γ to the
   * equation C[lγ]_p ≈ t | ψ, with data as given by step.  Note that, for a step to be created, it
   * is already given that l γ is indeed the subterm at the given position of the equation.  Hence,
   * the remaining checks are:
   * - check that all (meta-)vars in the rule are in dom(δ)
   * - check that ψ ⇒ φδ is valid
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    if (!checkEverythingSubstituted(module)) return false;
    if (!checkConstraintVariables(module)) return false;
    if (!checkImplication(module)) return false;
    return true;
  }

  /**
   * This function goes over all meta-variables in the step's rule, and ensures that they're all in
   * the domain of the step's substitution.  If not, we return false and print a failure message to
   * the user.
   *
   * Since it is already guaranteed that the left-hand side is fully mapped, we only consider the
   * replaceables in the right-hand side and constraint.
  */
  private boolean checkEverythingSubstituted(Optional<OutputModule> module) {
    TreeSet<Replaceable> missing = new TreeSet<Replaceable>();
    for (Replaceable x : _rule.queryRightSide().freeReplaceables()) {
      if (_substitution.get(x) == null) missing.add(x);
    }
    for (Replaceable x : _rule.queryConstraint().freeReplaceables()) {
      if (_substitution.get(x) == null) missing.add(x);
    }
    if (missing.isEmpty()) return true;
    StringBuilder builder = new StringBuilder();
    boolean first = true;
    for (Replaceable x : missing) {
      if (first) first = false; 
      else builder.append(", ");
      builder.append(_ruleRenaming.getName(x));
    }
    println(module, "Not enough information given: I could not determine the substitution to be " +
      "used for %a.", builder.toString());
    return false;
  }

  /**
   * This function goes over all the variables in the constraint of the rule, and verifies that they
   * are all mapped either to values by the substitution, or to variables in the constraint of the
   * equation.  The rule naming is used to print an error if this is not the case.
   */
  private boolean checkConstraintVariables(Optional<OutputModule> module) {
    Term constraint = _equ.getEquation().getConstraint();
    for (Variable x : _rule.queryConstraint().vars()) {
      Term t = _substitution.getReplacement(x);
      if (t.isValue()) continue;
      if (!t.isVariable() || !constraint.freeReplaceables().contains(t.queryVariable())) {
        Renaming eqnaming = _equ.getRenaming();
        println(module, "The rule does not apply: constraint variable %a is instantiated by %a, " +
          "which is not a value, nor a variable in the constraint of the equation.",
          _ruleRenaming.getName(x), new Pair<Term,Renaming>(t, eqnaming));
        return false;
      }
    }
    return true;
  }

  /**
   * For a rule l → r | φ, substitution δt and equation s ≈ t | ψ, this checks if ψ ⇒ φδ is valid.
   */
  private boolean checkImplication(Optional<OutputModule> module) {
    if (!_rule.isConstrained()) return true; // no implication to prove if the rule is unconstrained
    Term psi = _equ.getEquation().getConstraint();
    Term phidelta = _rule.queryConstraint().substitute(_substitution);
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(psi, phidelta);
    if (Settings.smtSolver.checkValidity(translator.queryProblem())) return true;
    Renaming renaming = _equ.getRenaming();
    println(module, "The rule does not apply: I could not prove that %a %{Vdash} %a.",
      new Pair<Term,Renaming>(psi, renaming), new Pair<Term,Renaming>(phidelta, renaming));
    return false;
  }

  @Override
  protected ProofState tryApply(Optional<OutputModule> module) {
    Term substituted = _rule.queryRightSide().substitute(_substitution);
    Equation equation = _equ.getEquation().replaceSubterm(_position, substituted);
    return _state.replaceTopEquation(_equ.replace(equation, _state.getLastUsedIndex() + 1));
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("simplify ", _ruleName, " ", _position, " with ",
      printer.makePrintable(_substitution, _ruleRenaming, _equ.getRenaming()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    Pair<Renaming,Renaming> renamings =
      new Pair<Renaming,Renaming>(_ruleRenaming, _equ.getRenaming());
    Pair<Substitution,Pair<Renaming,Renaming>> substitutionInfo =
      new Pair<Substitution,Pair<Renaming,Renaming>>(_substitution, renamings);
    module.println("We apply SIMPLIFICATION to %a with rule %a and substitution %a.",
      _equ.getName(), _ruleName, substitutionInfo);
  }
}

