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
import charlie.util.Pair;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;
import charlie.printer.PrinterFactory;
import charlie.smt.SmtSolver;
import charlie.theorytranslation.TermSmtTranslator;
import charlie.theorytranslation.TermAnalyser;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This class provides functionality that is used both by the SIMPLIFICATION and HYPOTHESIS
 * commands.
 *
 * The ConstrainedReductionHelper has information on a rule / hypothesis / other reducible object,
 * but also on the equation that it is applied on.  The ConstrainedReductionHelper is gradually
 * changed as more information about the appropriate substitution is discovered.  Hence, it cannot
 * be reused for another rule application, even with the same rule.
 */
class ConstrainedReductionHelper {
  private PartialProof _proof;
  private Term _left;
  private Term _right;
  private Term _constraint;
  private ArrayList<Pair<Variable,Term>> _definitions;
  private Renaming _renaming;
  private EquationPosition _position;
  private Substitution _substitution;
  private String _kind;
  private DeductionAlterDefinitions _preAlter;

  /**
   * Sets up the class from reduction using a "rule" left → right | constraint, where renaming is
   * used for printing the variables of the rule (when necessary).
   * The reduction will be done on the top equation in the current state of the partial proof, at
   * the given position, and with the given substitution or an extension thereof.  The given
   * substitution will not be altered, and will not become the property of this class; instead, it
   * will only be copied (and the copy may be changed by later calls on this object).  The renaming
   * will not be copied, but will not be altered by this class either.  This is the renaming used
   * to print the variables in left/right/constraint.
   *
   * The "kind" should either be "rule" or 'induction hypothesis" or something similar, to be
   * used in error messages.
   */
  ConstrainedReductionHelper(Term left, Term right, Term constraint, Renaming renaming, String kind,
                             PartialProof proof, EquationPosition pos, Substitution subst) {
    _left = left;
    _right = right;
    _renaming = renaming;
    _kind = kind;
    _proof = proof;
    _position = pos;
    _substitution = subst.copy();
    _constraint = constraint;
    _preAlter = null;
    _definitions = new ArrayList<Pair<Variable,Term>>();
    addEqualities(constraint, _definitions);
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
   * This returns the renaming specific to the current constrained reduction helper (to be used for
   * printing the (meta-)variables of the reducer object).  Outside objects should not change this
   * renaming.
   */
  Renaming queryRenaming() {
    return _renaming;
  }

  /**
   * This returns the substitution that underlies the current object.  Outside objects should not
   * change this substitution.
   */
  Substitution querySubstitution() {
    return _substitution;
  }

  /**
   * If an Alter step should be done before the reduction (and this was determined by a call to
   * makePreAlter), this returns the corresponding step; otherwise, it returns null.
   */
  DeductionAlterDefinitions queryPreAlter() {
    return _preAlter;
  }

  /** This returns a printable object representing the underlying substitution. */
  PrintableObject substitutionPrintable(Renaming equationRenaming) {
    return Printer.makePrintable(_substitution, _renaming, equationRenaming);
  }

  /**
   * Writing C[s]_p ≈ t | ψ for the top equation, where p is the underlying position, this method
   * extends the underlying substitution γ to a substitution δ so that _left δ = s, if possible.
   * If this is not possible, then an appropriate error message is given on m and false is
   * returned.  If it is possible, then in addition the rule's constraint is compared to the
   * equation's constraint for any obvious cases to add to the substitution, as the substitution
   * is required to cover all variables and meta-variables.
   */
  boolean extendSubstitution(Optional<OutputModule> m) {
    Equation eq = _proof.getProofState().getTopEquation().getEquation();
    
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

    if (_definitions.size() != 0) extendSubstitutionWithConstraintDefinitions(eq);
    
    return true;
  }

  /**
   * Helper function for extendSubstitution.  Given an equation C[s]_p ≈ t | ψ1 ∧...∧ ψn,
   * this updates _substitution by going through _definitions, and for each definition x = t with
   * x a variable that is not yet in the domain of _substitution: if all variables of t *are* in
   * _substitution, then one of three things will happen:
   * - if some ψj has the form y = t γ, then [x:=y] is added to the substitution
   * - if t γ is variable-free, then its value is computed and [x:=v] is added to the substitution
   * - if neither of those holds, nothing is done (in which case, checkEverythingSubstituted will
   *   fail unless something is done to extend the substitution later)
   *
   * Note that variables in the "rule" are only mapped to variables that already occur in the
   * equation.
   */
  private void extendSubstitutionWithConstraintDefinitions(Equation eq) {
    ArrayList<Pair<Variable,Term>> equEqualities = new ArrayList<Pair<Variable,Term>>();
    addEqualities(eq.getConstraint(), equEqualities);

    for (Pair<Variable,Term> pair : _definitions) {
      Variable x = pair.fst();
      Term t = pair.snd();
      if (_substitution.get(x) != null) continue;
      if (!allSubstituted(t)) continue;
      Term tgamma = t.substitute(_substitution);

      Term replacement = replaceByExistingClause(tgamma, equEqualities);
      //if (replacement == null) replacement = replaceByCalculation(tgamma);
      if (replacement != null) _substitution.extend(x, replacement);
    }
  }

  /** This returns whether all variables occurring in t are substituted. */
  private boolean allSubstituted(Term t) {
    for (Variable y : t.vars()) {
      if (_substitution.get(y) == null) return false;
    }
    return true;
  }

  /**
   * This helper function takes a constraint and adds all clauses that are equalities to the given
   * equalities list.
   */
  private void addEqualities(Term constraint, ArrayList<Pair<Variable,Term>> eqs) {
    if (!constraint.isFunctionalTerm()) return;
    CalculationSymbol calc = constraint.queryRoot().toCalculationSymbol();
    if (calc == null) return;
    if (calc.queryKind() == CalculationSymbol.Kind.AND) {
      for (int i = 1; i <= constraint.numberArguments(); i++) {
        addEqualities(constraint.queryArgument(i), eqs);
      }
    }
    else if (calc.queryKind() == CalculationSymbol.Kind.EQUALS ||
             calc.queryKind() == CalculationSymbol.Kind.IFF) {
      if (constraint.numberArguments() != 2) return;
      Term a = constraint.queryArgument(1);
      Term b = constraint.queryArgument(2);
      if (a.isVariable() && !_left.vars().contains(a.queryVariable())) {
        eqs.add(new Pair<Variable,Term>(a.queryVariable(), b));
      }
      else if (b.isVariable() && !_left.vars().contains(b.queryVariable())) {
        eqs.add(new Pair<Variable,Term>(b.queryVariable(), a));
      }
    }
  }

  /**
   * Helper function for extendSubstitutionWithConstraintDefinitions: if equEqualities contains an
   * equality y = tgamma, this returns y.  Otherwise it returns null.
   */
  private Variable replaceByExistingClause(Term tgamma,
                                           ArrayList<Pair<Variable,Term>> equEqualities) {
    for (Pair<Variable,Term> pair : equEqualities) {
      if (tgamma.equals(pair.snd())) return pair.fst();
    }
    return null;
  }

  /**
   * Helper function for extendSubstitutionWithConstraintDefinitions: if tgamma is a ground theory
   * term, this returns its value.  Otherwise it returns null.
   */
  private Value replaceByCalculation(Term tgamma) {
    if (tgamma.isGround() && tgamma.isTheoryTerm() && tgamma.queryType().isBaseType()) {
      return TermAnalyser.evaluate(tgamma);
    }
    return null;
  }

  /** 
   * Following extendSubstitution, if some definitions are not yet substituted, this function
   * creates a DeductionAlterDefinitions step that tries to add them to the substitution.  This
   * will create a "pre-alter" step which is stored internally, since the simplification step
   * should then be done on the result of the Alter step, rather than directly on an equation.
   * If there are no definitions left to substitute, this function will return false.
   */
  public boolean makePreAlter() {
    ArrayList<Pair<Pair<Variable,String>,Term>> adding =
      new ArrayList<Pair<Pair<Variable,String>,Term>>();
    Renaming renaming = _proof.getProofState().getTopEquation().getRenamingCopy();

    ArrayList<Variable> defined = new ArrayList<Variable>();
    for (Pair<Variable,Term> pair : _definitions) {
      Variable x = pair.fst();
      if (_substitution.get(x) != null) continue;
      Term t = pair.snd();
      if (!allSubstituted(t)) continue;
      Term tgamma = t.substitute(_substitution);

      Variable y =
        _proof.getContext().getVariableNamer().chooseDerivativeOrSameNaming(x, renaming,
                                                                            x.queryType());
      Pair<Variable,String> ypair = new Pair<Variable,String>(y, renaming.getName(y));
      adding.add(new Pair<Pair<Variable,String>,Term>(ypair, tgamma));
      _substitution.extend(x, y);
      defined.add(x);
    }
    
    if (adding.isEmpty()) return false;
    Optional<DeductionAlterDefinitions> ret = DeductionAlterDefinitions.createStep(_proof,
                                                                 Optional.empty(), adding);
    if (!ret.isPresent()) {
      for (Variable x : defined) _substitution.delete(x);
      return false;
    }
    _preAlter = ret.get();
    return true;
  }

  /**
   * This function goes over all meta-variables in _right and _constraint, and ensures that they're
   * all in the domain of the step's substitution.  If not, we return false and print a failure
   * message to the user.
   *
   * Note that this should be done AFTER extendSubstitution and perhaps makePreAlter, so that all
   * (meta-)variables whose mapping we can automatically deduce have already been included in the
   * domain of the substitution.
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
   * substitution _substitution to the top equation, assuming that we already know that the
   * subterm of equation at position _position is exactly _left _substitution.  That is, writing
   * ψ for the equation's constraint, we check that:
   * - all (meta-)vars in the rule's constraint (so: _constraint) are mapped to either values, or
   *   variables in Var(ψ)
   * - ψ ⇒ φδ is valid
   */
  boolean checkConstraintGoodForReduction(Optional<OutputModule> module, SmtSolver solver) {
    Term equationConstraint;
    Renaming equationRenaming;
    if (_preAlter == null) {
      EquationContext ec = _proof.getProofState().getTopEquation();
      equationConstraint = ec.getEquation().getConstraint();
      equationRenaming = ec.getRenamingCopy();
    }
    else {
      equationConstraint = _preAlter.queryUpdatedConstraint();
      equationRenaming = _preAlter.queryUpdatedRenaming();
    }
    if (!checkConstraintVariables(equationConstraint, equationRenaming, module)) return false;
    if (!checkImplication(equationConstraint, equationRenaming, module, solver)) return false;
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
      "%a %{Vdash} %a.", Printer.makePrintable(equationConstraint, eqrenaming),
      Printer.makePrintable(substitutedconstr, eqrenaming)));
    return false;
  }

  /**
   * Assuming that all prerequisites are satisfied to apply the "rule" _left → _right | _constraint
   * to equation at the underlying equation position, this returns the equation resulting from that
   * reduction.  (If there is a pre-alter step, the equation is also updated with the corresponding
   * constraint.)
   */
  Pair<Equation,Renaming> reduce() {
    Term substituted = _right.substitute(_substitution);
    Equation equation = _proof.getProofState().getTopEquation().getEquation();
    Equation ret = equation.replaceSubterm(_position, substituted);
    Renaming renaming;
    if (_preAlter == null) renaming = _proof.getProofState().getTopEquation().getRenamingCopy();
    else {
      ret = new Equation(ret.getLhs(), ret.getRhs(), _preAlter.queryUpdatedConstraint());
      renaming = _preAlter.queryUpdatedRenaming();
    }
    return new Pair<Equation,Renaming>(ret, renaming);
  }
}

