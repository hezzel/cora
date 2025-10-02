/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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

import java.util.ArrayList;
import java.util.Optional;
import java.util.TreeSet;
import java.util.function.Function;
import charlie.util.Pair;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.substitution.Substitution;
import charlie.trs.Rule;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** The deduction command for simplifying an equation with a Rule */
public final class DeductionSimplify extends DeductionStep {
  private String _ruleName;
  private EquationPosition _position;
  private DeductionAlterDefinitions _prealter;
  private ConstrainedSimplifier _simplifier;

  /** Private constructor, called (only) by createStep */
  private DeductionSimplify(ProofState state, ProofContext context, String ruleName,
                            EquationPosition pos, DeductionAlterDefinitions prealter,
                            ConstrainedSimplifier simpl) {
    super(state, context);
    _ruleName = ruleName;
    _position = pos;
    _prealter = prealter;
    _simplifier = simpl;
  }

  /**
   * Creates a simplification step for the given information, checking that there is indeed a
   * match but NOT that the constraint is satisfied or that no new variables are created.
   * The substitution will not be stored; it is safe to change afterwards.
   */
  public static DeductionSimplify createStep(PartialProof proof, Optional<OutputModule> m,
                                             String ruleName, EquationPosition pos,
                                             Substitution subst) {
    ProofContext context = proof.getContext();
    Rule rule = context.getRule(ruleName);
    if (rule == null) {
      m.ifPresent(o -> o.println("No such rule: %a.", ruleName));
      return null;
    }

    ConstrainedSimplifier simpl = new ConstrainedSimplifier(rule.queryLeftSide(),
      rule.queryRightSide(), rule.queryConstraint(), context.getRenaming(ruleName), subst);
    EquationContext equ = proof.getProofState().getTopEquation();

    if (!simpl.matchSubterm(equ.getEquation(), pos, m, "rule")) return null;
    DeductionAlterDefinitions prealter = null;
    if (!constraintFullySubstituted(equ.getConstraint(), simpl.querySubstitution())) {
      MutableRenaming ren = equ.getRenaming().copy();
      Function<Variable,Pair<Variable,String>> derivativeChooser = x -> {
        Variable y = context.getVariableNamer().chooseDerivativeOrSameNaming(x, ren, x.queryType());
        return new Pair<Variable,String>(y, ren.getName(y));
      };
      ArrayList<Pair<Pair<Variable,String>,Term>> definitions =
        simpl.addDefinitionsToSubstitution(derivativeChooser);
      if (definitions.size() > 0) {
        prealter = DeductionAlterDefinitions.createStep(proof, m, definitions);
      }
    }

    return new DeductionSimplify(proof.getProofState(), proof.getContext(), ruleName, pos,
                                 prealter, simpl);
  }

  /** Returns true if all variables in the constraint are substituted by subst. */
  private static boolean constraintFullySubstituted(Term constraint, Substitution subst) {
    for (Variable x : constraint.vars()) {
      if (subst.get(x) == null) return false;
    }
    return true;
  }

  /**
   * This function checks if we can indeed apply the rule l → r | φ with the substitution γ to the
   * equation C[lγ]_p ≈ t | ψ, with data as given by step.  Note that, for a step to be created, it
   * is already given that l γ is indeed the subterm at the given position of the equation.  Hence,
   * the remaining checks are:
   * - the rule applies to the constrained term lγ | ψ
   * - if we're required to be innermost, then the substitution is a semi-constructor one
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    // it needs to be an innermost step if we're using innermost strategy
    if ( (Settings.queryRewritingStrategy().equals(Settings.Strategy.Innermost) ||
          Settings.queryRewritingStrategy().equals(Settings.Strategy.CallByValue)) &&
         !_simplifier.checkSemiConstructorSubstitution(_pcontext) ) {
      module.ifPresent(o -> o.println("The rule can only be applied at an innermost position."));
      return false;
    }
    // the constraint implication should be satisfied
    if (_simplifier.constraintIsTrue()) return true;
    if (_prealter != null && !_prealter.verify(module)) return false;
    if (!_simplifier.checkEverythingSubstituted(module)) return false;
    Term constraint = _equ.getEquation().getConstraint();
    return _simplifier.canReduceCtermWithConstraint(constraint, Settings.smtSolver,
                                                    _equ.getRenaming(), module, "rule");
  }

  @Override
  protected ProofState tryApply(Optional<OutputModule> module) {
    Term substituted = _simplifier.queryReduct();
    Equation ret = _equ.getEquation().replaceSubterm(_position, substituted);
    Renaming renaming;
    if (_prealter == null) renaming = _equ.getRenaming();
    else {
      ret = new Equation(ret.getLhs(), ret.getRhs(), _prealter.queryUpdatedConstraint());
      renaming = _prealter.queryUpdatedRenaming();
    }
    EquationContext ec = _equ.replace(ret, renaming, _state.getLastUsedIndex() + 1);
    return _state.replaceTopEquation(ec);
  }


  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("simplify ", _ruleName, " ", _position, " with ",
      _simplifier.substitutionPrintable(_equ.getRenaming()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    if (_prealter == null) module.print("We apply SIMPLIFICATION to %a", _equ.getName());
    else {
      module.print("We apply ALTER to add %a to the constraint of %a, and then we apply " +
        "SIMPLIFICATION to the resulting equation",
        Printer.makePrintable(_prealter.queryAddedConstraint(), _prealter.queryUpdatedRenaming()),
        _equ.getName());
    }
    module.println(" with rule %a and substitution %a.",
      _ruleName, _simplifier.substitutionPrintable(_equ.getRenaming()));
  }
}

