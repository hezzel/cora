/**************************************************************************************************
 Copyright 2025 Cynthia Kop

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
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.*;
import charlie.substitution.Substitution;
import charlie.substitution.MutableSubstitution;
import charlie.substitution.Matcher;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;
import charlie.smt.SmtSolver;
import charlie.theorytranslation.TermSmtTranslator;
import charlie.theorytranslation.TermAnalyser;
import cora.io.OutputModule;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.ProofContext;

/**
 * This class provides functionality that is used by the SIMPLIFICATION, HYPOTHESIS and HDELETE
 * commands, to simplify a constrained term with a specific rule or equation.
 * 
 * Applying a rule (or hypothesis / other reducible object) l → r | φ to a constrained term
 * s | ψ at the root in principle takes the following steps:
 * - the constraint ψ is adapted to an equi-satisfiable constraint ψ', by adding fresh variable
 *   definitions y = t to the constraint
 * - we compute γ so that s = l γ and ψ' ⇒ φγ, and reduce to the new constrained term r γ | ψ'
 *
 * Moreover, since we assume quasi-reductivity and inextensible theory sorts, we assume that all
 * variables of theory sort in s can only be instantiated by values; hence, they are treated as
 * though they are initially in ψ.
 * 
 * In practice, the extension of ψ into ψ' is done alongside the finding of a suitable substitution
 * γ, and there are multiple strategies to extend ψ.  So, this is done gradually, with the results
 * stored as part of the ConstrainedSimplifier.
 *
 * Hence, the ConstrainedSimplifier is specific to one application of the rule; it cannot be reused
 * for another, even with the same rule.
 */
class ConstrainedSimplifier {
  private Term _left;
  private Term _right;
  private Term _constraint;
  private Renaming _renaming;
  private MutableSubstitution _substitution;

  /**
   * We may choose to split off some equalities of the form x = t from _constraint (in this case
   * they are removed from _constraint and moved into _definitions).  This does not always happen,
   * but is used for some strategies of simplification.  However, the constraint given by
   * _constraint ∧ { x = t for <x,t> in _definitions } is always equivalent to the original
   * constraint given to the constructor of the class.
   */
  private ArrayList<Pair<Variable,Term>> _definitions;

  /**
   * Sets up the class for reduction using a "rule" left → right | constraint, where renaming is
   * used for printing the variables of the rule (when necessary).
   * 
   * The given substitution is an initial _partial_ substitution that should be applied to the
   * variables of the rule, and is allowed to be null (for an empty substitution); variables that
   * occur in the rule but are not in the domain will still need to be assigned for the rule to be
   * applied.  The substitution (if given) does not become the property of this class but is only
   * copied; hence, the original may freely be changed by the calling object.
   * 
   * The renaming will not be copied, and therefore becomes included in this class; outside objects
   * should not alter it later on (or risk changing the ConstrainedSimplifier as well).  This is
   * the renaming used to print the variables in left/right/constraint.
   *
   * The "kind" should either be "rule" or 'induction hypothesis" or something similar, to be
   * used in error messages.
   */
  ConstrainedSimplifier(Term left, Term right, Term constraint, Renaming renaming,
                        Substitution subst) {
    _left = left;
    _right = right;
    _renaming = renaming.makeImmutable();
    _substitution = subst == null ? new MutableSubstitution() : subst.copy();
    _definitions = new ArrayList<Pair<Variable,Term>>();
    _constraint = splitEqualities(constraint, _definitions);
  }

  /**
   * This helper function takes a constraint φ1 ∧...∧ φn, and for each φi of the form x = t
   * or t = x, stores it in equalities.  It returns the conjunction of those clauses φi that
   * are not of this form, so that returnvalue ∧ equalities is equivalent to the original
   * constraint.
   */
  private Term splitEqualities(Term constraint, ArrayList<Pair<Variable,Term>> equalities) {
    if (!constraint.isFunctionalTerm()) return constraint;
    if (constraint.numberArguments() != 2) return constraint;
    CalculationSymbol calc = constraint.queryRoot().toCalculationSymbol();
    if (calc == null) return constraint;
    if (calc.queryKind() == CalculationSymbol.Kind.AND) {
      Term a = splitEqualities(constraint.queryArgument(1), equalities);
      Term b = splitEqualities(constraint.queryArgument(2), equalities);
      return TheoryFactory.createConjunction(a, b);
    }
    if (calc.queryKind() != CalculationSymbol.Kind.EQUALS &&
        calc.queryKind() != CalculationSymbol.Kind.IFF) return constraint;
    Term a = constraint.queryArgument(1);
    Term b = constraint.queryArgument(2);
    if (a.isVariable()) {
      equalities.add(new Pair<Variable,Term>(a.queryVariable(), b));
      return TheoryFactory.trueValue;
    }
    if (b.isVariable()) {
      equalities.add(new Pair<Variable,Term>(b.queryVariable(), a));
      return TheoryFactory.trueValue;
    }
    return constraint;
  }

  /**
   * This returns the (unmodifiable) renaming specific to the current constrained reduction helper
   * (to be used for printing the (meta-)variables of the reducer object).
   */
  Renaming queryRenaming() {
    return _renaming;
  }

  /**
   * This returns the substitution that underlies the current object.  Outside objects cannot
   * change this substitution.
   */
  Substitution querySubstitution() {
    return _substitution.makeImmutable();
  }

  /** This returns a printable object representing the underlying substitution. */
  PrintableObject substitutionPrintable(Renaming equationRenaming) {
    return Printer.makePrintable(_substitution, _renaming, equationRenaming);
  }

  /** This returns whether the constraint for the underlying rule is True. */
  boolean constraintIsTrue() {
    return _constraint.isValue() && _constraint.toValue().getBool() &&
           _definitions.isEmpty();
  }

  /**
   * This function goes over all replaceables in the underlying rule, and returns those that are
   * not yet in the domain of the step's substitution.
  */
  TreeSet<Replaceable> queryMissingReplaceables() {
    TreeSet<Replaceable> missing = new TreeSet<Replaceable>();
    for (Replaceable x : _left.freeReplaceables()) {
      if (_substitution.get(x) == null) missing.add(x);
    }
    for (Replaceable x : _right.freeReplaceables()) {
      if (_substitution.get(x) == null) missing.add(x);
    }
    for (Replaceable x : _constraint.freeReplaceables()) {
      if (_substitution.get(x) == null) missing.add(x);
    }
    for (Pair<Variable,Term> pair : _definitions) {
      if (_substitution.get(pair.fst()) == null) missing.add(pair.fst());
      for (Replaceable x : pair.snd().freeReplaceables()) {
        if (_substitution.get(x) == null) missing.add(x);
      }
    }
    return missing;
  }

  /**
   * This returns true if all values mapped to by the current state of the substitution are
   * semi-constructor terms.  This is needed if we are to use innermost or call-by-value
   * reduction.
   */
  boolean checkSemiConstructorSubstitution(ProofContext context) {
    for (Replaceable x : _substitution.domain()) {
      Term result = _substitution.get(x);
      for (var pair : result.querySubterms()) {
        Term t = pair.fst();
        if (!t.isFunctionalTerm()) continue;
        FunctionSymbol f = t.queryRoot();
        if (f.toCalculationSymbol() == null && !context.getTRS().isDefined(f)) continue;
        if (context.queryRuleArity(f) <= t.numberArguments()) return false;
      }
    }
    return true;
  }

  /**
   * This fixes the underlying substitution to a copy of the given one.  If subst == null, then
   * the empty substitution will be stored instead.
   */
  void replaceSubstitution(Substitution subst) {
    if (subst == null) _substitution = new MutableSubstitution();
    else _substitution = subst.copy();
  }

  /**
   * This function extends _substitution so that _left _substitution = s, if possible, and in that
   * case, returns null.  If not possible, then an appropriate failure is returned.
   *
   * Note that in BOTH cases, the underlying _substitution may have been updated, so if you wish
   * to reuse the ConstrainedSimplifier to match another term against the same rule, then you
   * should call replaceSubstitution first to restore the original substitution.
   */
  Matcher.MatchFailure matchLeft(Term s) {
    return Matcher.extendMatch(_left, s, _substitution);
  }

  /**
   * This function extends _substitution so that _right _substitution = s, if possible, and in that
   * case, returns null.  If not possible, then an appropriate failure is returned.
   *
   * Note that in BOTH cases, the underlying _substitution may have been updated, so if you wish to
   * reuse the ConstrainedSimplifier to match another term against the same rule, then you should
   * call replaceSubstitution first to restore the original substitution.
   */
  Matcher.MatchFailure matchRight(Term t) {
    return Matcher.extendMatch(_right, t, _substitution);
  }

  /**
   * Given that the underlying rule has a form l → r | φ1 ∧...∧ φn, we consider all clauses φi of
   * the form x = t, where x is a variable that has not yet been substituted, while all variables
   * in t have been substituted.  We find a mapping for x if one of the following holds:
   * - The given constraint psi contains a clause y = t _substitution; then we map x to y.
   * - t _substitution is ground; then we compute the corresponding value v and map x to v.
   * We do this for all definitions in the underlying rule's constraint, from left to right.
   *
   * We return true if anything was added to the substitution, false if not.
   *
   * This is useful when reducing a constrained term s | ψ: all variables in the rule's constraint
   * must be substituted, so we look to ψ to find an instantiation such that ψ ⇒ φi _substitution
   * holds.
   */
  boolean matchEqualitiesInConstraint(Term psi) {
    ArrayList<Pair<Variable,Term>> eqs = new ArrayList<Pair<Variable,Term>>();
    splitEqualities(psi, eqs);
    boolean anythingAdded = false;
    for (Pair<Variable,Term> myPair : _definitions) {
      Variable x = myPair.fst();
      if (_substitution.get(x) != null) continue;
      Term t = myPair.snd();
      if (!allSubstituted(t)) continue;
      Term tgamma = _substitution.substitute(t);
      Term result = null;
      for (Pair<Variable,Term> pair : eqs) {
        if (tgamma.equals(pair.snd())) { result = pair.fst(); break; }
      }
      if (result == null) result = calculateGroundTerm(tgamma);
      if (result != null) {
        anythingAdded = true;
        _substitution.extend(x, result);
      }
    }
    return anythingAdded;
  }

  /** This returns the term _right _substitution. */
  Term queryReduct() {
    return _substitution.substitute(_right);
  }

  /**
   * Given that the underlying rule has a form l → r | φ1 ∧...∧ φn, we consider all clauses φi of
   * the form x = t, where x is a variable that has not yet been substituted, while all variables
   * in t have been substituted.  For each such x, we create a fresh variable y and extend the
   * substitution with [x:=y].  The return value contains all pairs (y, t _substitution) that were
   * added.
   *
   * The derivativeChooser should, given the variable x, create a fresh variable y and choose its
   * name.
   *
   * This is useful for a ~ step, or Alter step in rewriting induction: when simplifying a
   * constrained term we may first replace it by an equivalent one.  Adding y = t _substitution to
   * the constraint does not affect the possible instantiations of the constrained term, since we
   * are working in a setting where we may assume all theory variables are instantiated by values.
   */
  ArrayList<Pair<Pair<Variable,String>,Term>> addDefinitionsToSubstitution(
                                      Function<Variable,Pair<Variable,String>> derivativeChooser) {
    ArrayList<Pair<Pair<Variable,String>,Term>> ret =
      new ArrayList<Pair<Pair<Variable,String>,Term>>();
    for (Pair<Variable,Term> pair : _definitions) {
      Variable x = pair.fst();
      if (_substitution.get(x) != null) continue;
      Term t = pair.snd();
      if (!allSubstituted(t)) continue;
      Term tgamma = _substitution.substitute(t);
      Pair<Variable,String> ypair = derivativeChooser.apply(x);
      ret.add(new Pair<Pair<Variable,String>,Term>(ypair, tgamma));
      _substitution.extend(x, ypair.fst());
    }
    return ret;
  }

  /**
   * This returns whether all variables occurring in t are substituted.
   * (Helper function for matchEqualitiesInConstraint.)
   */
  private boolean allSubstituted(Term t) {
    for (Variable y : t.vars()) {
      if (_substitution.get(y) == null) return false;
    }
    return true;
  }

  /**
   * If t is a base-type ground theory term, then this returns the corresponding value.  If not, it
   * returns null.
   * (Helper function for matchEqualitiesInConstraint.)
   */
  private Value calculateGroundTerm(Term t) {
    if (t.isGround() && t.isTheoryTerm() && t.queryType().isBaseType()) {
      return TermAnalyser.evaluate(t);
    }
    return null;
  }

  /**
   * Writing C[s]_pos ≈ t | ψ for the given equation, where p is the underlying position, this
   * method extends the underlying substitution γ to a substitution δ so that _left δ = s, if
   * possible.
   * 
   * If this is not possible, then an appropriate error message is given on m and false is
   * returned -- but it might still be the case that _substitution has been changed.  If it is
   * possible, then those variable mappings that are needed for the left-hand side are included
   * in the substitution.
   */
  boolean matchSubterm(Equation eq, EquationPosition pos,
                       Optional<OutputModule> m, String kind) {
    Term s = eq.querySubterm(pos);
    if (s == null) {
      m.ifPresent(o -> o.println("No such position: %a.", pos));
      return false;
    }

    Matcher.MatchFailure problem = Matcher.extendMatch(_left, s, _substitution);
    if (problem != null) {
      m.ifPresent(o -> o.println("The " + kind + " does not apply due to failed matching " +
        "(matching debug info says: %a)", Printer.makePrintable(problem, _renaming)));
      return false;
    }

    return true;
  }

  /**
   * This function checks if we can apply the rule _left → _right | _constraint with the
   * substitution _substitution to a term _left _substitution | psi.  That is, we check that:
   * - all (meta-)vars in _constraint are mapped to either values, or to variables
   *   (while it is technically required that they are mapped to a variable in ψ, we drop this
   *   constraint here because in the RI framework we may always assume that theory variables are
   *   instantiated by values)
   * - ψ ⇒ φ _substitution is valid
   */
  boolean canReduceCtermWithConstraint(Term psi, SmtSolver solver, Renaming psiNaming,
                                       Optional<OutputModule> module, String kind) {
    if (!checkConstraintVariables(psi, psiNaming, module, kind)) return false;
    if (!checkImplication(psi, psiNaming, solver, module, kind)) return false;
    return true;
  }

  /**
   * This function goes over all the variables in _constraint and _definitions, and verifies that
   * they are all mapped either to values or variables by the substitution.
   */
  private boolean checkConstraintVariables(Term equationConstraint, Renaming equationNaming,
                                           Optional<OutputModule> module, String kind) {
    TreeSet<Variable> vars = new TreeSet<Variable>();
    for (Variable x : _constraint.vars()) vars.add(x);
    for (Pair<Variable,Term> pair : _definitions) {
      vars.add(pair.fst());
      for (Variable x : pair.snd().vars()) vars.add(x);
    }
    for (Variable x : vars) {
      Term t = _substitution.get(x);
      if (t == null) {
        module.ifPresent(o -> o.println("The " + kind + " does not apply: constraint variable " +
          "%a is not mapped to anything.", _renaming.getName(x)));
        return false;
      }
      if (!t.isValue() && !t.isVariable()) {
        module.ifPresent(o -> o.println("The " + kind + " does not apply: constraint variable " +
          "%a is instantiated by %a, which is not a value or variable.",
          _renaming.getName(x), Printer.makePrintable(t, equationNaming)));
        return false;
      }
    }
    return true;
  }

  /** This checks if psi ⇒ (_constraint ∧ _definitions) _substitution is valid. */
  private boolean checkImplication(Term psi, Renaming psirenaming, SmtSolver solver,
                                   Optional<OutputModule> module, String kind) {
    Term c = _constraint;
    for (Pair<Variable,Term> d : _definitions) {
      c = TheoryFactory.createConjunction(c, TheoryFactory.createEquality(d.fst(), d.snd()));
    }
    Term substitutedconstr = _substitution.substitute(c);
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(psi, substitutedconstr);
    if (solver.checkValidity(translator.queryProblem())) return true;
    
    if (module.isPresent()) {
      ArrayList<Term> badConstraints = new ArrayList<Term>();
      storeUnsatisfiedConstraints(psi, substitutedconstr, badConstraints, solver);
      OutputModule m = module.get();
      m.print("The " + kind + " does not apply: I could not prove that ");
      for (int i = 0; i < badConstraints.size(); i++) {
        if (i != 0) m.print(" nor ");        
        m.print("%a %{Vdash} %a", Printer.makePrintable(psi, psirenaming),
          Printer.makePrintable(badConstraints.get(i), psirenaming));
      }
      m.println(".");
    }
    return false;
  }

  /**
   * Helper function for checkImplication: given that conclusion = φ1 ∧...∧ φn, this stores those
   * φi into storage for which premise ⇒ φi is not valid.
   */
  private void storeUnsatisfiedConstraints(Term premise, Term conclusion,
                                           ArrayList<Term> storage, SmtSolver solver) {
    if (conclusion.isFunctionalTerm()) {
      CalculationSymbol calc = conclusion.queryRoot().toCalculationSymbol();
      if (calc != null && calc.queryKind() == CalculationSymbol.Kind.AND) {
        for (int i = 1; i <= conclusion.numberArguments(); i++) {
          storeUnsatisfiedConstraints(premise, conclusion.queryArgument(i), storage, solver);
        }
        return;
      }
    }

    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(premise, conclusion);
    if (!solver.checkValidity(translator.queryProblem())) storage.add(conclusion);
  }

  /**
   * This function checks if all replaceables in the underlying rule are substituted, and if not,
   * returns false and prints a failure message to the user.
  */
  boolean checkEverythingSubstituted(Optional<OutputModule> module) {
    TreeSet<Replaceable> missing = queryMissingReplaceables();
    if (missing.isEmpty()) return true;
    if (!module.isPresent()) return false;
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
}

