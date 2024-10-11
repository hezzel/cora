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

package cora.termination.reduction_pairs.horpo;

import charlie.util.Pair;
import charlie.types.*;
import charlie.terms.*;
import charlie.smt.*;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.termination.reduction_pairs.*;
import cora.termination.reduction_pairs.horpo.HorpoConstraintList.HRelation;
import cora.termination.reduction_pairs.horpo.HorpoConstraintList.HorpoRequirement;

import java.util.List;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * The HorpoSimplifier is a helper class for the Horpo reduction pair.
 * It captures all the data relevant to a Horpo problem: the _parameters, argument filtering,
 * constraint list and SMT problem.  It can be used to simplify a single HorpoRequirement (from the
 * constraint list), which potentially affects all of the above.
 */
class HorpoSimplifier {
  private final HorpoParameters _parameters;
  private final HorpoConstraintList _hcl;
  private final ArgumentFilter _filter;
  private final SmtProblem _smt;
  private int _counter; // only for human-readable output in the SmtProblem

  HorpoSimplifier(HorpoParameters params, HorpoConstraintList lst, ArgumentFilter filter) {
    _parameters = params;
    _hcl = lst;
    _filter = filter;
    _smt = _parameters.queryProblem();
    _counter = 0;
  }

  /**
   * The main Horpo functionality: this takes a HorpoRequirement, and adds SMT requirements that
   * guarantee <defining variable> ⇒ requirement holds to _smt.  In doing so, it may be that
   * additional HorpoRequirements with their defining variables are added to the
   * HorpoConstraintList _hcl, and these must also be defined before the SMT problem truly
   * implies the truth of the definition.
   */
  void simplify(HorpoRequirement req) {
    switch (req.relation()) {
      case HRelation.GREATER:       handleGreater(req); break;
      case HRelation.GREATERTHEORY: handleTheory(req); break;
      case HRelation.GREATERVAR:    handleVar(req); break;
      case HRelation.GREATERFUN:    handleFun(req); break;
      case HRelation.GREATERRPO:    handleGrRpo(req); break;
      case HRelation.GEQ:           handleGeq(req); break;
      case HRelation.GEQTHEORY:     handleTheory(req); break;
      case HRelation.GEQVAR:        handleVar(req); break;
      case HRelation.GEQFUN:        handleFun(req); break;
      case HRelation.GEQEQUAL:      handleEqual(req); break;
      case HRelation.GEQNOGR:       handleGeqNoGr(req); break;
      case HRelation.GEQNOGRTHEORY: handleTheory(req); break;
      case HRelation.GEQNOGRVAR:    handleVar(req); break;
      case HRelation.GEQNOGRFUN:    handleFun(req); break;
      case HRelation.GEQNOGREQUAL:  handleEqual(req); break;
      case HRelation.RPO:           handleRpo(req); break;
      case HRelation.RPOSELECT:     handleSelect(req); break;
      case HRelation.RPOCOPY:       handleCopy(req); break;
      case HRelation.RPOLEX:        handleLex(req); break;
      case HRelation.RPOMUL:        handleMul(req); break;
      case HRelation.RPOTH:         handleRpoTh(req); break;
    }
  }

  /**
   * Returns whether or not a and b are equal modulo renaming of base types.
   * Here, we treat product types as base types.
   */
  private boolean sameTypeStructure(Type a, Type b) {
    return switch (a) {
      case Base _, Product _ -> switch (b) {
        case Base _, Product _ -> true;
        case Arrow _ -> false;
      };
      case Arrow(Type in1, Type out1) -> switch (b) {
        case Base _, Product _ -> false;
        case Arrow(Type in2, Type out2) ->
          sameTypeStructure(in1, in2) && sameTypeStructure(out1, out2);
      };
    };
  }

  /** Helper function for brevity: requires one of the given constraints in the SmtProblem */
  private void requireOr(Constraint ...args) {
    _smt.require(SmtFactory.createDisjunction(args));
  }

  /***********************************************************************************************/
  /* The functions below all serve to simplify different kinds of HorpoRequirements.             */
  /***********************************************************************************************/

  /**
   * This simplifies requirements of the form: left ≻ right | constraint by delegating to
   * sub-relations such as ≻{rpo}.
   */
  private void handleGreater(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    // the GREATER relation is only allowed to compare terms with the same type structure
    if (!sameTypeStructure(l.queryType(), r.queryType())) {
      _smt.require(req.variable().negate()); return;
    }
    // shortcut: if l = r, this can never hold
    if (l.equals(r)) { _smt.require(req.variable().negate()); return; }

    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    if (l.isTheoryTerm()) {
      _smt.requireImplication(req.variable(), _hcl.store(l, HRelation.GREATERTHEORY, r, c, v));
    }
    else {
      requireOr(req.variable().negate(),
                _hcl.store(l, HRelation.GREATERRPO, r, c, v),
                _hcl.store(l, HRelation.GREATERVAR, r, c, v),
                _hcl.store(l, HRelation.GREATERFUN, r, c, v));
    }
  }

  /**
   * This simplifies requirements of the form: left ≽ right | constraint by delegating to
   * sub-relations such as ≽{mono}.
   */
  private void handleGeq(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    // the GEQ relation is only allowed to compare terms with the same type structure
    if (!sameTypeStructure(l.queryType(), r.queryType())) {
      _smt.require(req.variable().negate()); return;
    }

    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    // if l = r, then we only try GEQEQUAL (which will succeed)
    if (l.equals(r)) {
      _smt.requireImplication(req.variable(), _hcl.store(l, HRelation.GEQEQUAL, r, c, v));
    }
    // otherwise, for theory terms, only GEQTHEORY can apply
    else if (l.isTheoryTerm()) {
      _smt.requireImplication(req.variable(), _hcl.store(l, HRelation.GEQTHEORY, r, c, v));
    }
    // for non-theory terms, only the other options apply; instead of GREATER we immediately go to
    // GREATERRPO, because the other "GREATER" options are already covered by GEQVAR and GEQFUN
    else {
      requireOr(req.variable().negate(),
                _hcl.store(l, HRelation.GREATERRPO, r, c, v),
                _hcl.store(l, HRelation.GEQVAR, r, c, v),
                _hcl.store(l, HRelation.GEQFUN, r, c, v));
    }
  }

  /**
   * This simplifies requirements of the form: left ≈ right | constraint by delegating to
   * sub-relations (such as ≈{theory}).
   */
  private void handleGeqNoGr(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    // the GEQNOGR relation is only allowed to compare terms with the same type structure
    if (!sameTypeStructure(l.queryType(), r.queryType())) {
      _smt.require(req.variable().negate()); return;
    }

    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    // if l = r, then we only try GEQEQUAL (which will succeed)
    if (l.equals(r)) {
      _smt.requireImplication(req.variable(), _hcl.store(l, HRelation.GEQNOGREQUAL, r, c, v));
    }
    // otherwise, for theory terms, only GEQNOGRTHEORY can apply
    else if (l.isTheoryTerm()) {
      _smt.requireImplication(req.variable(), _hcl.store(l, HRelation.GEQNOGRTHEORY, r, c, v));
    }
    else {
      requireOr(req.variable().negate(),
                _hcl.store(l, HRelation.GEQNOGRVAR, r, c, v),
                _hcl.store(l, HRelation.GEQNOGRFUN, r, c, v));
    }
  }

  /**
   * This simplifies requirements of the form: left ▷ right | constraint by delegating to
   * sub-relations (such as ▷{copy}).
   * Note: by construction, any HorpoRequirements with an RPO shape necessarily have a
   * functional term as left-hand side.
   */
  private void handleRpo(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    requireOr(req.variable().negate(),
              _hcl.store(l, HRelation.RPOTH, r, c, v),
              _hcl.store(l, HRelation.RPOSELECT, r, c, v),
              _hcl.store(l, HRelation.RPOCOPY, r, c, v),
              _hcl.store(l, HRelation.RPOLEX, r, c, v),
              _hcl.store(l, HRelation.RPOMUL, r, c, v));
  }

 /**
   * This adds the requirement for:
   * - definingVariable <--> phi ⊨ l ⊐ r if the relation is GREATERTHEORY
   * - definingVariable <--> phi ⊨ l ⊒ r if the relation is GEQTHEORY
   * - definingVariable <--> phi ⊨ l ⊒ r but not phi ⊨ l ⊐ r for GEQNOGRTHEORY
   * Here, ⊐ is the ordering on integers given by the HorpoParameters.  If an inequality cannot be
   * proven, we assume that it is false (which therefore allows a false positive for GEQNOGRTHEORY).
   *
   * We specifically use <--> instead of the usual --> here because in this case, it is easy to do,
   * and it is needed for the GeqNoGr case.
   *
   * Note: by construction, any HorpoRequirements with one of these shapes necessarily have a
   * theory term as left-hand side.
   */
  private void handleTheory(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    Term phi = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    BVar variable = req.variable();
    HRelation relation = req.relation();
    if (!theoryAllowed(l, r, v)) _smt.require(variable.negate());
    else if (relation == HRelation.GEQNOGRTHEORY) {
      BVar x = _hcl.store(l, HRelation.GEQTHEORY, r, phi, v);
      BVar y = _hcl.store(l, HRelation.GREATERTHEORY, r, phi, v);
      _smt.require(SmtFactory.createIff(variable,
        SmtFactory.createConjunction(x, y.negate())));
    }
    else if (l.queryType().equals(TypeFactory.intSort)) {
      handleIntComparison(l, r, phi, variable, relation, _parameters);
    }
    else if (l.queryType().equals(TypeFactory.boolSort)) {
      handleBoolComparison(l, r, phi, variable, relation, _parameters);
    }
    else _smt.require(variable.negate());
  }

  /** Returns whether s is a base-type theory term with all its variables in theoryVariables */
  private boolean isTheory(Term s, TreeSet<Variable> theoryVariables) {
    if (!s.isTheoryTerm() || !s.queryType().isBaseType() ||
        !s.queryType().isTheoryType()) return false;
    for (Replaceable x : s.freeReplaceables()) {
      if (!theoryVariables.contains(x)) return false;
    }
    return true;
  }

  /** Returns whether we are even allowed to apply one of the theory cases */
  private boolean theoryAllowed(Term l, Term r, TreeSet<Variable> theoryVariables) {
    return isTheory(l, theoryVariables) && isTheory(r, theoryVariables);
  }

  /**
   * To handle an integer comparison, we check whether φ ⇒ l ≥ r is valid in the case of a
   * GEQTHEORY comparison, or φ ⇒ l > r ∧ l ≥ -M is valid in the case of GREATER.
   * We check the same for φ ⇒ l ≤ r and φ ⇒ l < r ∧ l ≤ M.
   * Then, we use this to create an <--> formula stating that the defining variable x holds if and
   * only if the corresponding inequality is provable for the value of
   * _parameters.getDirectionIsDownVariable().
   *
   * We use a separate SMT problem to do the validity check, as it should not be a part of the
   * satisfiability problem.
   */
  private void handleIntComparison(Term l, Term r, Term phi, BVar x, HRelation rel,
                                   HorpoParameters _parameters) {
    SmtProblem validityProblem = new SmtProblem();
    TermSmtTranslator tst = new TermSmtTranslator(validityProblem);
    IntegerExpression el = tst.translateIntegerExpression(l);
    IntegerExpression er = tst.translateIntegerExpression(r);
    Constraint c = tst.translateConstraint(phi);

    Constraint downProblem, upProblem;
    if (rel == HRelation.GREATERTHEORY) {
      IntegerExpression eMM = SmtFactory.createValue(-_parameters.queryIntegerBound());
      downProblem = SmtFactory.createConjunction(  // l > r ∧ l ≥ -M
        SmtFactory.createGreater(el, er), SmtFactory.createGeq(el, eMM) );
      eMM = SmtFactory.createValue(_parameters.queryIntegerBound());
      upProblem = SmtFactory.createConjunction(    // l < r ∧ l ≤ M
        SmtFactory.createSmaller(el, er), SmtFactory.createLeq(el, eMM) );
    }
    else {
      downProblem = SmtFactory.createGeq(el, er);
      upProblem = SmtFactory.createLeq(el, er);
    }

    validityProblem.requireImplication(c, downProblem);
    boolean downValid = Settings.smtSolver.checkValidity(validityProblem);
    validityProblem.clear();
    validityProblem.requireImplication(c, upProblem);
    boolean upValid = Settings.smtSolver.checkValidity(validityProblem);

    if (downValid && upValid) _smt.require(x);
    else if (downValid) {
      _smt.require(SmtFactory.createIff(x, _parameters.getDirectionIsDownVariable()));
    }
    else if (upValid) {
      _smt.require(SmtFactory.createIff(x,
        _parameters.getDirectionIsDownVariable().negate()));
    }
    else _smt.require(x.negate());
  }

  /**
   * For boolean comparisons, we fix true ⊐ false (as this case rarely occurs anyway).
   * Thus, we check if left ∧ ¬right (for strict comparison) or left ∨ ¬right (for weak comparison)
   * is valid, and force the value of x accordingly, so that x <--> left <rel> right.
   *
   * We use a separate SMT problem to do the validity check, as it should not be a part of the
   * satisfiability problem.
   */
  private void handleBoolComparison(Term l, Term r, Term phi, BVar x, HRelation rel,
                                    HorpoParameters _parameters) {
    SmtProblem validityProblem = new SmtProblem();
    TermSmtTranslator tst = new TermSmtTranslator(validityProblem);
    Constraint cl = tst.translateConstraint(l);
    Constraint cr = tst.translateConstraint(r);
    Constraint cp = tst.translateConstraint(phi);
    Constraint negr = SmtFactory.createNegation(cr);

    Constraint constr;
    if (rel == HRelation.GREATERTHEORY) constr = SmtFactory.createConjunction(cl, negr);
    else constr = SmtFactory.createDisjunction(cl, negr);
    validityProblem.requireImplication(cp, constr);

    if (Settings.smtSolver.checkValidity(validityProblem)) _smt.require(x);
    else _smt.require(x.negate());
  }

  /**
   * This is only called for ≽ and ≈ requirements where we already know that both sides are
   * equal, so this just forces the defining variable of the requirement to true.
   */
  private void handleEqual(HorpoRequirement req) {
    _smt.require(req.variable());
  }

  /**
   * This adds the defining constraints for var requirements:
   * - x(s1,...,sn) ≈{mono} x(t1,...,tn) implies that each si ≈ ti
   * - x(s1,...,sn) ≽{var} x(t1,...,tn) and x(s1,...,sn) ≻{var} x(t1,...,tn) imply that each si ≽ ti
   * - x(s1,...,sn) ≻{var} x(t1,...,tn) moreover implies that (1) nothing is filtered, and (2)
   *   some si ≻ ti
   *
   * Note: by construction, any HorpoRequirements with one of these shapes necessarily have a
   * non-theory term as left-hand side.
   */
  private void handleVar(HorpoRequirement req) {
    Term left = req.left();
    Term right = req.right();
    int n = left.numberArguments();

    if (!left.isVarTerm() || n != right.numberArguments() ||
        !left.queryHead().equals(right.queryHead())) {
      _smt.require(req.variable().negate());
      return;
    }

    HRelation subrel = req.relation() == HRelation.GEQNOGRVAR ? HRelation.GEQNOGR : HRelation.GEQ;
    for (int i = 1; i <= n; i++) {
      BVar x = _hcl.store(left.queryArgument(i), subrel, right.queryArgument(i),
                          req.constraint(), req.theoryVariables());
      _smt.requireImplication(req.variable(), x);
    }

    if (req.relation() == HRelation.GREATERVAR) {
      _smt.requireImplication(req.variable(), _filter.regardsEverything());
      ArrayList<Constraint> oneof = new ArrayList<Constraint>(n);
      for (int i = 1; i <= n; i++) {
        oneof.add(_hcl.store(left.queryArgument(i), HRelation.GREATER, right.queryArgument(i),
                             req.constraint(), req.theoryVariables()));
      }
      _smt.requireImplication(req.variable(), SmtFactory.createDisjunction(oneof));
    }
  }

  /**
   * This adds the defining constraints for fun requirements:
   * - f(s1,...,sk) ≈{fun} g(t1,...,tn)
   * - g(s1,...,sk) ≽{fun} g(t1,...,tn)
   * - g(s1,...,sn) ≻{fun} g(t1,...,tn)
   *
   * By construction, any HorpoRequirements with one of these shapes necessarily have a non-theory
   * term as left-hand side.
   */
  private void handleFun(HorpoRequirement req) {
    Term left = req.left();
    Term right = req.right();
    if (!left.isFunctionalTerm() || !right.isFunctionalTerm()) {
      _smt.require(req.variable().negate());
      return;
    }

    FunctionSymbol f = left.queryRoot();
    FunctionSymbol g = right.queryRoot();
    int k = left.numberArguments();
    int n = right.numberArguments();
    _counter++;  // update the fresh variable counter, since some fresh variables are going to
                 // be created (e.g., for χ), and we want to give them a new name
    requireOr(req.variable().negate(), SmtFactory.createEqual(_parameters.getPrecedence(f),
                                                              _parameters.getPrecedence(g)));
    requireFunRest(f, k, g, n, req.variable());
    ArrayList<IVar> chi = createChiForFun(f, k, g, n, req.variable());
    requireInjective(k, g, n, req.variable(), chi);
    requireSamePermutation(f, k, g, n, req.variable(), chi);
    requireChiGeq(k, n, req, chi,
                  req.relation() == HRelation.GEQNOGRFUN ? HRelation.GEQNOGR : HRelation.GEQ);

    if (req.relation() == HRelation.GREATERFUN) requireChiGreater(f, k, n, req, chi);
    else if (req.relation() == HRelation.GEQNOGRFUN) {
      requireChiSurjective(f, k, n, req.variable(), chi);
    }
  }

  /**
   * Helper function for handleGeq: all <REL>{fun} requirements have the condition that arity(f) - k
   * = arity(g) - n, and that writing m := arity(f) - k we have:
   *   for 1 ≤ i ≤ m: π{f}(k+i) = π{g}(n+i) ∨ π{g}(n+i) = 0
   * Here we require this conditional on reqvar
   */
  private void requireFunRest(FunctionSymbol f, int k, FunctionSymbol g, int n, BVar reqvar) {
    int m = f.queryArity() - k;
    if (m != g.queryArity() - n) { _smt.require(reqvar.negate()); return; }
    for (int i = 1; i <= m; i++) {
      IVar gni = _parameters.getPermutation(g, n + i);
      Constraint equal = SmtFactory.createEqual(gni, _parameters.getPermutation(f, k + i));
      Constraint zero = SmtFactory.createEqual(gni, SmtFactory.createValue(0));
      _smt.requireImplication(reqvar, SmtFactory.createDisjunction(equal, zero));
    }
  }

  /**
   * Helper function for handleFun: creates a function χ from {1..n} to {0..k} such that
   * - if reqvar then χ maps i with i ∉ regards[g] to 0
   * - if reqvar then χ maps i with i ∉ regards[g] to something non-zero
   */
  private ArrayList<IVar> createChiForFun(FunctionSymbol f, int k, FunctionSymbol g, int n,
                                          BVar reqvar) {
    ArrayList<IVar> ret = new ArrayList<IVar>(n);
    IntegerExpression zero = SmtFactory.createValue(0);
    IntegerExpression one = SmtFactory.createValue(1);
    IntegerExpression kk = SmtFactory.createValue(k);
    // create the variables for χ, and require that χ maps i with i ∉ regards[g] to 0,
    // and χ maps i with i ∉ regards[g] to an element j of {1..k}
    for (int i = 1; i <= n; i++) {
      IVar chi_i = _smt.createIntegerVariable("chi" + _counter + "(" + i + ")");
      ret.add(chi_i);
      // 0 ≤ χ(i) ≤ k -- the 0 ≤ χ(i) part is redundant, but may help the solver
      _smt.require(SmtFactory.createGeq(chi_i, zero));
      _smt.require(SmtFactory.createLeq(chi_i, kk));
      // if regards[g,i] then χ(i) ≥ 1 else χ(i) = 0
      requireOr(reqvar.negate(), _filter.regards(g,i).negate(), SmtFactory.createGeq(chi_i, one));
      requireOr(reqvar.negate(), _filter.regards(g,i), SmtFactory.createEqual(chi_i, zero));
    }
    return ret;
  }

  /**
   * Helper function for handleFun: this requires that, if reqvar holds, then χ is injective on
   * {1..n} ∩ regards[g], where χ is already known to map regarded elements of {1..n} into {1..k},
   * and disregarded elements to 0.
   *
   * Here, chi(i) is represented by chi.get(i-1).
   */
  private void requireInjective(int k, FunctionSymbol g, int n, BVar reqvar, ArrayList<IVar> chi) {
    for (int i = 1; i < n; i++) {
      IVar chi_i = chi.get(i-1);
      for (int j = i+1; j <= n; j++) {
        IVar chi_j = chi.get(j-1);
        requireOr(reqvar.negate(), _filter.regards(g,i).negate(),
                  SmtFactory.createUnequal(chi_i, chi_j));
      }
    }
  }

  /**
   * Helper function for handleFun: this requires that, if reqvar holds, then for all i ∈ {1..n}
   * ∩ regards[g] we have π{f}(χ(i)) = π{g}(i), where χ is already known to map regarded elements
   * of {1..n} into {1..k} and disregarded elements to 0.  Note that this implies that regarded
   * elements of g are mapped to regarded elements of f.
   *
   * Here, chi(i) is represented by chi.get(i-1).
   */
  private void requireSamePermutation(FunctionSymbol f, int k, FunctionSymbol g, int n, BVar reqvar,
                                      ArrayList<IVar> chi) {
    for (int i = 1; i <= n; i++) {
      IVar chi_i = chi.get(i-1);
      // χ(i) is regarded if and only if χ(i) = j for some j ∈ {1..k}
      for (int j = 1; j <= k; j++) {
        requireOr(reqvar.negate(), SmtFactory.createUnequal(chi_i, SmtFactory.createValue(j)),
          SmtFactory.createEqual(_parameters.getPermutation(f,j), _parameters.getPermutation(g,i))
        );
      }
    }
  }

  /**
   * Helper function for handleFun: this requires that, for all i ∈ {1..n} such that χ(i) = j ∈
   * {1..k}, we have s_j <rel> t_i, where s_j is argument j of the left-hand side of the
   * requirement, and t_i is argument i of the right-hand side of the requirement.
   */
  private void requireChiGeq(int k, int n, HorpoRequirement req, List<IVar> chi, HRelation rel) {
    Term left = req.left();
    Term right = req.right();
    Term constr = req.constraint();
    TreeSet<Variable> tvar = req.theoryVariables();
    for (int i = 1; i <= n; i++) {
      IVar chi_i = chi.get(i-1);
      for (int j = 1; j <= k; j++) {
        BVar comp = _hcl.store(left.queryArgument(j), rel, right.queryArgument(i), constr, tvar);
        requireOr(req.variable().negate(), 
          SmtFactory.createUnequal(chi_i, SmtFactory.createValue(j)), comp);
      }
    }
  }

  /**
   * Helper function for handleFun: this requires that either χ is not surjective, or there is
   * some i such that s_{χ(i)} ≻ t_i.  This exactly means that there is one a ∈ {1..k} ∩ regards[f]
   * such that IF a = χ(i) THEN s_a ≻ t_i.  Note that if there is no i such that a = χ(i), then
   * clearly χ is not surjective, so this suffices.
   */
  private void requireChiGreater(FunctionSymbol f, int k, int n, HorpoRequirement req,
                                 List<IVar> chi) {
    ArrayList<Constraint> parts = new ArrayList<Constraint>();

    // a ∈ {1..k}
    IVar a = _smt.createIntegerVariable("decrease" + _counter);
    _smt.requireImplication(req.variable(), SmtFactory.createGeq(a, SmtFactory.createValue(1)));
    _smt.requireImplication(req.variable(), SmtFactory.createLeq(a, SmtFactory.createValue(k)));
    // a ∈ regards[f], so ∀ j ∈ {1..k}. a = j ⇒ j ∈ regards[f]
    for (int j = 1; j <= k; j++) {
      requireOr(req.variable().negate(),
                SmtFactory.createUnequal(a, SmtFactory.createValue(j)),
                _filter.regards(f, j));
    }
    // ∀ i ∈ {1..n}. ∀ j ∈ {1..k}. χ(i) = j ∧ j = a ⇒ left_j ≻ right_i
    Term left = req.left();
    Term right = req.right();
    Term constr = req.constraint();
    TreeSet<Variable> tvar = req.theoryVariables();
    for (int i = 1; i <= n; i++) {
      IVar chi_i = chi.get(i-1);
      for (int j = 1; j <= k; j++) {
        BVar sjgreaterti = _hcl.store(left.queryArgument(j), HRelation.GREATER,
                                      right.queryArgument(i), constr, tvar);
        requireOr(req.variable().negate(),
                  SmtFactory.createUnequal(chi_i, a),
                  SmtFactory.createUnequal(a, SmtFactory.createValue(j)),
                  sjgreaterti);
      }
    }
  }

  /**
   * Helper function for handleFun: this requires that for all j ∈ {1..k} ∩ regards[f] there exists
   * some i ∈ {1..n} such that χ(i) = k, provided reqvar holds.
   */
  private void requireChiSurjective(FunctionSymbol f, int k, int n, BVar reqvar, List<IVar> chi) {
    for (int j = 1; j <= k; j++) {
      ArrayList<Constraint> parts = new ArrayList<Constraint>(n+2);
      parts.add(reqvar.negate());
      parts.add(_filter.regards(f,j).negate());
      IntegerExpression jj = SmtFactory.createValue(j);
      for (int i = 1; i <= n; i++) parts.add(SmtFactory.createEqual(chi.get(i-1), jj));
      _smt.require(SmtFactory.createDisjunction(parts));
    }
  }

  /**
   * This simplifies requirements of the form l ≻{rpo} r | φ by delegating to ▷ -- provided
   * the requirement satisfies the conditions to be used in ▷.
   */
  private void handleGrRpo(HorpoRequirement req) {
    if (!req.left().isFunctionalTerm() || req.left().isTheoryTerm()) {
      _smt.require(req.variable().negate());
    }
    else {
      if (req.left().queryType().isArrowType()) {
        FunctionSymbol f = req.left().queryRoot();
        // all additional parameters should be regarded
        int m = f.queryArity();
        for (int i = req.left().numberArguments() + 1; i <= m; i++) {
          _smt.requireImplication(req.variable(), _filter.regards(f, i));
        }
      }
      BVar x = _hcl.store(req.left(), HRelation.RPO, req.right(), req.constraint(),
                         req.theoryVariables());
      _smt.requireImplication(req.variable(), x);
    }
  }

  /**
   * This simplifies requirements of the form l ▷{select} r by finding an immediate subterm li of
   * l such that r = a r_1...r_n with li ≽ a and l ▷ each r_j.  This is a limitation of the full
   * Select rule, where we omit the possibility of using f* (for now).
   */
  private void handleSelect(HorpoRequirement req) {
    Term l = req.left();
    FunctionSymbol f = l.queryRoot();
    int k = l.numberArguments();

    Term r = req.right();
    int n = r.numberArguments();
    int rest = r.queryType().queryArity();
    int m = n + rest; // total arity of h

    ArrayList<Constraint> options = new ArrayList<Constraint>(k + 1);
    options.add(req.variable().negate());

    for (int i = 1; i <= k; i++) {
      Constraint c = createSelectConstraint(l,f,i,r,n,m,req.constraint(), req.theoryVariables());
      if (c != null) options.add(c);
    }
    _smt.require(SmtFactory.createDisjunction(options));
  }

  /**
   * Helper function for handleSelect: this creates a requirement indicating that if
   * left = f(l_1,...,l_k) and right = h(r_1,...,r_n) :: σ_{n+1} →...→ s_m → ι, then there is
   * some i such that l_{index} ≽ h(r_1,...,i) and left ▷ r_j for i < j ≤ n.
   */
  private Constraint createSelectConstraint(Term left, FunctionSymbol f, int index,
                                            Term right, int n, int m,
                                            Term constr, TreeSet<Variable> tvar) {
    Term arg = left.queryArgument(index);
    int p = arg.queryType().queryArity();

    if (p < m - n) return null;   // arg has a greater arity than right => select rule inapplicable
    if (p > m) return null;       // can't do this ntil we implement the f* construct
    ArrayList<Constraint> allof = new ArrayList<Constraint>(2 + p - n + m);
    allof.add(_filter.regards(f, index));
    Term head = right.queryImmediateHeadSubterm(m - p);
    allof.add(_hcl.store(arg, HRelation.GEQ, head, constr, tvar));
    for (int j = m - p + 1; j <= n; j++) {
      allof.add(_hcl.store(left, HRelation.RPO, right.queryArgument(j), constr, tvar));
    }
    return SmtFactory.createConjunction(allof);
  }

  /**
   * Helper function: this requires that req.left ▷ t_i for every regarded argument t_i of
   * req.right().  Here, req.right() is required to be a functional term.
   */
  private void requireLeftGreaterRightArguments(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    FunctionSymbol g = r.queryRoot();
    for (int i = 1; i <= r.numberArguments(); i++) {
      BVar subreq = _hcl.store(l, HRelation.RPO, r.queryArgument(i), req.constraint(),
                               req.theoryVariables());
      BVar regards = _filter.regards(g, i);
      requireOr(req.variable().negate(), _filter.regards(g, i).negate(), subreq);
    }
  }

  /**
   * This simplifies requirements of the form l ▷{copy} r by requiring the precedences are
   * well-ordered, and that l ▷ each of the arguments of r.
   */
  private void handleCopy(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    FunctionSymbol f = l.queryRoot();
    if (!r.isFunctionalTerm() || r.queryRoot().equals(f) || isTheory(r, req.theoryVariables())) {
      // theory terms are excluded here because they are already covered by thterm (plus,
      // calculation symbols at the head of a theory term may not be included in the precedence)
      _smt.require(req.variable().negate());
    }
    else {
      FunctionSymbol g = r.queryRoot();
      IVar predf = _parameters.getPrecedence(f);
      IVar predg = _parameters.getPrecedence(g);
      _smt.requireImplication(req.variable(),
        SmtFactory.createGreater(predf, predg));
      requireLeftGreaterRightArguments(req);
    }
  }

  /**
   * This simplifies requirements of the form l ▷{th} r: the defining variable is forced to true
   * if r is a theory term with only theory variables, and to false otherwise.
   */
  private void handleRpoTh(HorpoRequirement req) {
    Term r = req.right();
    boolean isgood = r.isTheoryTerm();
    if (isgood) {
      for (Variable x : r.vars()) {
        if (!req.theoryVariables().contains(x)) { isgood = false; break; }
      }
    }
    if (isgood) _smt.require(req.variable());
    else _smt.require(req.variable().negate());
  }

  private void handleLex(HorpoRequirement req) {
    // TODO
    _smt.require(req.variable().negate());
  }

  private void handleMul(HorpoRequirement req) {
    // TODO
    _smt.require(req.variable().negate());
  }
}


