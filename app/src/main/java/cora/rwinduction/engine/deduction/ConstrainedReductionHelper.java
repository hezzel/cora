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

import java.util.Optional;
import java.util.TreeSet;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;
import charlie.printer.PrinterFactory;
import charlie.smt.SmtSolver;
import charlie.theorytranslation.TermSmtTranslator;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This class provides functionality that is used both by the SIMPLIFICATION and HYPOTHESIS
 * commands.
 */
class ConstrainedReductionHelper {
  private Term _left;
  private Term _right;
  private Term _constraint;
  private Renaming _renaming;
  private EquationPosition _position;
  private Substitution _substitution;
  private String _kind;

  /**
   * Sets up the class from reduction using a "rule" left → right | constraint, where renaming is
   * used for printing (when necessary) and name to represent the name of this rule or hypothesis.
   * The reduction will be done at the given position, and with the given substitution or an
   * extension thereof.  The given substitution will not be altered, and will not become the
   * property of this class; instead, it will only be copied,
   *
   * The "kind" should either be "rule" or 'induction hypothesis" or something similar, to bbe
   * used in error messages.
   */
  ConstrainedReductionHelper(Term left, Term right, Term constraint, Renaming renaming,
                             EquationPosition pos, Substitution subst, String kind) {
    _left = left;
    _right = right;
    _constraint = constraint;
    _renaming = renaming;
    _position = pos;
    _substitution = subst.copy();
    _kind = kind;
  }

  /** This returns whether the constraint for the underlying rule is True. */
  boolean constraintIsTrue() {
    return _constraint.isValue() && _constraint.toValue().getBool();
  }

  /** This returns the EquationPosition that underlies the current object. */
  EquationPosition queryPosition() {
    return _position;
  }

  /**
   * This returns the substitution that underlies the current object.  The caller should not change
   * this substitution; it is the property of this class.
   */
  Substitution querySubstitution() {
    return _substitution;
  }

  /** This returns a printable object representing the underlying substitution. */
  PrintableObject substitutionPrintable(Renaming equationRenaming) {
    return Printer.makePrintable(_substitution, _renaming, equationRenaming);
  }

  /**
   * Writing C[s]_p ≈ t | ψ for eq, where p is the underlying position, this method extends the
   * underlying substitution γ to a substitution δ so that _left δ = s, if possible.  If this is
   * not possible, then an appropriate error message is given on m and false is returned.
   */
  boolean extendSubstitution(Equation eq, Optional<OutputModule> m) {
    Term s = eq.querySubterm(_position);
    if (s == null) {
      m.ifPresent(o -> o.println("No such position: %a.", _position));
      return false;
    }

    String problem = _left.match(s, _substitution);
    if (problem != null) {
      m.ifPresent(o -> o.println("The " + _kind + " does not apply: %a", problem));
      return false;
    }
    
    return true;
  }

  /**
   * This function goes over all meta-variables in _right and _constraint, and ensures that they're
   * all in the domain of the step's substitution.  If not, we return false and print a failure
   * message to the user.
   *
   * Note that this is not technically _necessary_, but if these are not mapped, we have to choose
   * what to map them to, and for now this choice has not been implemented: if the right-hand side
   * or constraint contain (meta-)variables that do not occur on the left, the user has to supply
   * their substituted value.
  */
  boolean checkEverythingSubstituted(Optional<OutputModule> module) {
    TreeSet<Replaceable> missing = new TreeSet<Replaceable>();
    for (Replaceable x : _right.freeReplaceables()) {
      if (_substitution.get(x) == null) missing.add(x);
    }
    for (Replaceable x : _constraint.freeReplaceables()) {
      if (_substitution.get(x) == null) missing.add(x);
    }
    if (missing.isEmpty()) return true;
    StringBuilder builder = new StringBuilder();
    boolean first = true;
    for (Replaceable x : missing) {
      if (first) first = false; 
      else builder.append(", ");
      builder.append(_renaming.getName(x));
    }
    module.ifPresent(m -> m.println("Not enough information given: I could not determine the " +
      "substitution to be used for %a.", builder.toString()));
    return false;
  }

  /**
   * This function checks if we can indeed apply the rule _left → _right | _constraint with the
   * substitution _substitution to the given equation, assuming that we already know that the
   * subterm of equation at position _position is exactly _left _substitution.  That is, writing
   * ψ for the equation's constraint, we check that:
   * - all (meta-)vars in the rule's constraint (so: _constraint( are mapped to either values, or
   *   variables in Var(ψ)
   * - ψ ⇒ φδ is valid
   */
  boolean checkConstraintGoodForReduction(Term equationConstraint, Renaming eqrenaming,
                                          Optional<OutputModule> module, SmtSolver solver) {
    if (!checkConstraintVariables(equationConstraint, eqrenaming, module)) return false;
    if (!checkImplication(equationConstraint, eqrenaming, module, solver)) return false;
    return true;
  }

  /**
   * This function goes over all the variables in _constraint, and verifies that they are all
   * mapped either to values by the substitution, or to variables in the constraint of the
   * equation.  If this is not the case, an error message is printed and false returned.
   */
  private boolean checkConstraintVariables(Term equationConstraint, Renaming equationNaming,
                                           Optional<OutputModule> module) {
    for (Variable x : _constraint.vars()) {
      Term t = _substitution.getReplacement(x);
      if (t.isValue()) continue;
      if (!t.isVariable() || !equationConstraint.freeReplaceables().contains(t.queryVariable())) {
        module.ifPresent(o -> o.println("The " + _kind + " does not apply: constraint variable " +
          "%a is instantiated by %a, which is not a value, nor a variable in the constraint of " +
          "the equation.", _renaming.getName(x), Printer.makePrintable(t, equationNaming)));
        return false;
      }
    }
    return true;
  }

  /** This checks if equationConstraint ⇒ _constraint _substitution is valid. */
  private boolean checkImplication(Term equationConstraint, Renaming eqrenaming,
                                   Optional<OutputModule> module, SmtSolver solver) {
    Term substitutedconstr = _constraint.substitute(_substitution);
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(equationConstraint, substitutedconstr);
    if (solver.checkValidity(translator.queryProblem())) return true;
    module.ifPresent(o -> o.println("The " + _kind + " does not apply: I could not prove that " +
      "%a %{Vdash} %a.", Printer.makePrintable(equationConstraint, _renaming),
      Printer.makePrintable(substitutedconstr, eqrenaming)));
    return false;
  }

  /**
   * Assuming that all prerequisites are satisfied to apply the "rule" _left → _right | _constraint
   * to equation at the underlying equation position, this returns the equation resulting from that
   * reduction.
   */
  Equation reduce(Equation equation, Optional<OutputModule> module) {
    Term substituted = _right.substitute(_substitution);
    return equation.replaceSubterm(_position, substituted);
  }
}

