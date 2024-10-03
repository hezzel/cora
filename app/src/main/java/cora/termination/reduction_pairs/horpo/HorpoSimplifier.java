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
 * It captures all the data relevant to a Horpo problem: the _parameters, monotonicity requirements,
 * constraint list and SMT problem.  It can be used to simplify a single HorpoRequirement (from the
 * constraint list), which potentially affects all of the above.
 */
class HorpoSimplifier {
  private final HorpoParameters _parameters;
  private final HorpoConstraintList _hcl;
  private final Monotonicity _monotonicity;
  private final SmtProblem _smt;

  HorpoSimplifier(HorpoParameters params, HorpoConstraintList lst, Monotonicity mono) {
    _parameters = params;
    _hcl = lst;
    _monotonicity = mono;
    _smt = _parameters.queryProblem();
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
      case HRelation.GREATERMONO:   handleGrMono(req); break;
      case HRelation.GREATERARGS:   handleArgs(req); break;
      case HRelation.GREATERRPO:    handleGrRpo(req); break;
      case HRelation.GEQ:           handleGeq(req); break;
      case HRelation.GEQTHEORY:     handleTheory(req); break;
      case HRelation.GEQEQUAL:      handleEqual(req); break;
      case HRelation.GEQMONO:       handleMono(req); break;
      case HRelation.GEQARGS:       handleArgs(req); break;
      case HRelation.GEQNOGR:       handleGeqNoGr(req); break;
      case HRelation.GEQNOGRTHEORY: handleTheory(req); break;
      case HRelation.GEQNOGREQUAL:  handleEqual(req); break;
      case HRelation.GEQNOGRMONO:   handleMono(req); break;
      case HRelation.GEQNOGRARGS:   handleArgs(req); break;
      case HRelation.RPO:           handleRpo(req); break;
      case HRelation.RPOSELECT:     handleSelect(req); break;
      case HRelation.RPOAPPL:       handleAppl(req); break;
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
      _smt.require(req.variable().negate());
      return;
    }
    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    ArrayList<Constraint> lst = new ArrayList<Constraint>(3);
    // for theory terms, only Relation.GREATERTHEORY applies; for non-theory terms, only the
    // other options apply
    if (l.isTheoryTerm()) lst.add(_hcl.store(l, HRelation.GREATERTHEORY, r, c, v));
    else {
      lst.add(_hcl.store(l, HRelation.GREATERRPO, r, c, v));
      lst.add(_hcl.store(l, HRelation.GREATERMONO, r, c, v));
      lst.add(_hcl.store(l, HRelation.GREATERARGS, r, c, v));
    }
    Constraint combi = SmtFactory.createDisjunction(lst);
    _smt.requireImplication(req.variable(), combi);
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
      _smt.require(req.variable().negate());
      return;
    }
    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    ArrayList<Constraint> lst = new ArrayList<Constraint>(3);
    // for theory terms, only GEQTHEORY and GEQEQUAL apply; for non-theory terms, only the other
    // options apply
    if (l.isTheoryTerm()) {
      lst.add(_hcl.store(l, HRelation.GEQTHEORY, r, c, v));
      lst.add(_hcl.store(l, HRelation.GEQEQUAL, r, c, v));
    }
    else {
      lst.add(_hcl.store(l, HRelation.GREATERRPO, r, c, v));
      lst.add(_hcl.store(l, HRelation.GEQMONO, r, c, v));
      lst.add(_hcl.store(l, HRelation.GEQARGS, r, c, v));
    }
    Constraint combi = SmtFactory.createDisjunction(lst);
    _smt.requireImplication(req.variable(), combi);
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
      _smt.require(req.variable().negate());
      return;
    }
    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    ArrayList<Constraint> lst = new ArrayList<Constraint>(2);
    // for theory terms, only GEQNOGRTHEORY and GEQNOGREQUAL apply; for non-theory terms, only the
    // other options apply
    if (l.isTheoryTerm()) {
      lst.add(_hcl.store(l, HRelation.GEQNOGRTHEORY, r, c, v));
      lst.add(_hcl.store(l, HRelation.GEQNOGREQUAL, r, c, v));
    }
    else {
      lst.add(_hcl.store(l, HRelation.GEQNOGRMONO, r, c, v));
      lst.add(_hcl.store(l, HRelation.GEQNOGRARGS, r, c, v));
    }
    Constraint combi = SmtFactory.createDisjunction(lst);
    _smt.requireImplication(req.variable(), combi);
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
    ArrayList<Constraint> lst = new ArrayList<Constraint>(6);
    lst.add(_hcl.store(l, HRelation.RPOTH, r, c, v));
    lst.add(_hcl.store(l, HRelation.RPOSELECT, r, c, v));
    lst.add(_hcl.store(l, HRelation.RPOCOPY, r, c, v));
    lst.add(_hcl.store(l, HRelation.RPOLEX, r, c, v));
    lst.add(_hcl.store(l, HRelation.RPOMUL, r, c, v));
    lst.add(_hcl.store(l, HRelation.RPOAPPL, r, c, v));
    Constraint combi = SmtFactory.createDisjunction(lst);
    _smt.requireImplication(req.variable(), combi);
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

  /** Returns whether we are even allowed to apply one of the theory cases */
  private boolean theoryAllowed(Term l, Term r, TreeSet<Variable> theoryVariables) {
    if (!l.isTheoryTerm() || !r.isTheoryTerm() || !l.queryType().isBaseType() ||
        !l.queryType().isTheoryType() || !l.queryType().equals(r.queryType())) {
      return false;
    }
    ReplaceableList lvars = l.freeReplaceables();
    ReplaceableList rvars = r.freeReplaceables();
    for (Replaceable x : lvars) if (!theoryVariables.contains(x)) return false;
    for (Replaceable x : rvars) if (!theoryVariables.contains(x)) return false;
    return true;
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

  private void handleEqual(HorpoRequirement req) {
    if (req.left().equals(req.right())) _smt.require(req.variable());
    else _smt.require(req.variable().negate());
  }

  /**
   * For now, this method simply adds a constraint that the given requirement is not satisfied.
   * In the future, this may be used for NON-FILTERING reduction pairs to allow a strict decrease
   * in a varterm.
   * TODO
   */
  private void handleGrMono(HorpoRequirement req) {
    _smt.require(req.variable().negate());
  }

  /**
   * This adds the defining constraints for mono requirements:
   * - x(s1,...,sn) ≽{mono} x(t1,...,tn) if each si ≽ ti
   * - x(s1,...,sn) ≈{mono} x(t1,...,tn) if each si ≈ ti
   *
   * Note: by construction, any HorpoRequirements with one of these shapes necessarily have a
   * non-theory term as left-hand side.
   */
  private void handleMono(HorpoRequirement req) {
    Term left = req.left();
    Term right = req.right();

    if (!left.isVarTerm() || left.numberArguments() != right.numberArguments() ||
        !left.queryHead().equals(right.queryHead())) {
      _smt.require(req.variable().negate());
      return;
    }

    HRelation subrel = req.relation() == HRelation.GEQNOGRMONO ? HRelation.GEQNOGR : HRelation.GEQ;
    for (int i = 1; i <= left.numberArguments(); i++) {
      BVar x = _hcl.store(left.queryArgument(i), subrel, right.queryArgument(i),
                         req.constraint(), req.theoryVariables());
      _smt.requireImplication(req.variable(), x);
    }
  }

  /**
   * This adds the defining constraints for args requirements:
   * - f(s1,...,sn) ≽{args} f(t1,...,tn) if each unfiltered si ≽ ti
   * - f(s1,...,sn) ≻{args} f(t1,...,tn) if each unfiltered si ≽ ti and some unfiltered si ≻ ti
   * - f(s1,...,sn) ≈{args} f(t1,...,tn) if each unfiltered si ≈ ti
   * Here, position i is unfiltered if either a is a variable, or a is a function symbol that
   * regards position i.
   *
   * Note: by construction, any HorpoRequirements with one of these shapes necessarily have a
   * non-theory term as left-hand side.
   *
   * TODO: this needs to be updated to take equivalent function symbols (with the same filter list)
   * into account
   */
  private void handleArgs(HorpoRequirement req) {
    Term left = req.left();
    Term right = req.right();

    if (!left.isFunctionalTerm() || left.numberArguments() != right.numberArguments() ||
        !left.queryHead().equals(right.queryHead())) {
      _smt.require(req.variable().negate());
      return;
    }

    HRelation subrel = req.relation() == HRelation.GEQNOGRARGS ? HRelation.GEQNOGR : HRelation.GEQ;
    FunctionSymbol f = left.queryRoot();
    for (int i = 1; i <= left.numberArguments(); i++) {
      BVar x = _hcl.store(left.queryArgument(i), subrel, right.queryArgument(i),
                              req.constraint(), req.theoryVariables());
      BVar regards = _monotonicity.regards(f, i);
      _smt.requireImplication(req.variable(), SmtFactory.createDisjunction(
        regards.negate(), x));
    }

    if (req.relation() == HRelation.GREATERARGS) {
      ArrayList<Constraint> onestrict = new ArrayList<Constraint>();
      for (int i = 1; i <= left.numberArguments(); i++) {
        BVar x = _hcl.store(left.queryArgument(i), HRelation.GREATER, right.queryArgument(i),
                                req.constraint(), req.theoryVariables());
        BVar regards = _monotonicity.regards(f, i);
        onestrict.add(SmtFactory.createConjunction(regards, x));
      }
      _smt.requireImplication(req.variable(), SmtFactory.createDisjunction(onestrict));
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
        int m = f.queryArity();
        for (int i = req.left().numberArguments() + 1; i <= m; i++) {
          _smt.requireImplication(req.variable(), _monotonicity.regards(f, i));
        }
      }
      BVar x = _hcl.store(req.left(), HRelation.RPO, req.right(), req.constraint(),
                         req.theoryVariables());
      _smt.requireImplication(req.variable(), x);
    }
  }

  private void handleSelect(HorpoRequirement req) {
    Term l = req.left();
    FunctionSymbol f = l.queryRoot();
    ArrayList<Constraint> args = new ArrayList<Constraint>(l.numberArguments());
    for (int i = 1; i <= l.numberArguments(); i++) {
      BVar x = _monotonicity.regards(f, i);
      Term a = l.queryArgument(i);
      BVar y = _hcl.store(a, HRelation.GEQ, req.right(), req.constraint(), req.theoryVariables());
      args.add(SmtFactory.createConjunction(x, y));
    }

    if (args.size() == 0) { _smt.require(req.variable().negate()); return; }
    else _smt.requireImplication(req.variable(),SmtFactory.createDisjunction(args));
  }

  private void handleAppl(HorpoRequirement req) {
    Term r = req.right();
    if (r.numberArguments() == 0) {
      _smt.require(req.variable().negate());
      return;
    }
    Term a = r.queryImmediateHeadSubterm(r.numberArguments()-1);
    Term b = r.queryArgument(r.numberArguments());
    _smt.requireImplication(req.variable(),
      _hcl.store(req.left(), HRelation.RPO, a, req.constraint(), req.theoryVariables()));
    _smt.requireImplication(req.variable(),
      _hcl.store(req.left(), HRelation.RPO, b, req.constraint(), req.theoryVariables()));
  }

  /**
   * Helper function: this requires that req.left ▷ t_i for every regarded argument t_i of
   * req.right with i ≥ start.  Here, req.right is required to be a functional term.
   */
  private void requireLeftGreaterRightArguments(HorpoRequirement req, int start) {
    Term l = req.left();
    Term r = req.right();
    FunctionSymbol g = r.queryRoot();
    for (int i = start; i <= r.numberArguments(); i++) {
      BVar subreq = _hcl.store(l, HRelation.RPO, r.queryArgument(i), req.constraint(),
                                   req.theoryVariables());
      BVar regards = _monotonicity.regards(g, i);
      _smt.requireImplication(req.variable(),
        SmtFactory.createDisjunction(regards.negate(), subreq));
    }
  }

  private void handleCopy(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    FunctionSymbol f = l.queryRoot();
    if (!r.isFunctionalTerm() || r.queryRoot().equals(f) || r.isValue()) {
      // values are excluded here because this case is already covered by thterm
      _smt.require(req.variable().negate());
    }
    else {
      FunctionSymbol g = r.queryRoot();
      IVar predf = _parameters.getPrecedenceFor(f);
      IVar predg = _parameters.getPrecedenceFor(g);
      _smt.requireImplication(req.variable(),
        SmtFactory.createGreater(predf, predg));
      requireLeftGreaterRightArguments(req, 1);
    }
  }

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
    Term l = req.left();
    Term r = req.right();
    if (!r.isFunctionalTerm()) {
      _smt.require(req.variable().negate());
      return; 
    }   
    FunctionSymbol f = l.queryRoot();
    FunctionSymbol g = r.queryRoot();
    // get the maximum relevant number of arguments; this should be at least 1
    int m = l.numberArguments();
    if (r.numberArguments() < m) m = r.numberArguments();
    if (m == 0) { _smt.require(req.variable().negate()); return; }
    // to apply lex, both function symbols should have the same precedence
    _smt.requireImplication(req.variable(),
      SmtFactory.createEqual(_parameters.getPrecedenceFor(f), _parameters.getPrecedenceFor(g)));
    // moreover, they should both have Lex status
    _smt.requireImplication(req.variable(),
      SmtFactory.createEqual(_parameters.getStatusFor(f), SmtFactory.createValue(1)));
    _smt.requireImplication(req.variable(),
      SmtFactory.createEqual(_parameters.getStatusFor(g), SmtFactory.createValue(1)));
    // if there is only one argument, the decrease should be there
    if (m == 1) {
      _smt.requireImplication(req.variable(), _monotonicity.regards(f, 1));
      _smt.requireImplication(req.variable(), _monotonicity.regards(g, 1));
      _smt.requireImplication(req.variable(), _hcl.store(l.queryArgument(1), HRelation.GREATER,
                                 r.queryArgument(1), req.constraint(), req.theoryVariables()));
    }   
    else handleLexComplicated(f, g, m, l, r, req);
  }

  /**
   * Helper function for handleLex: handles the case where we actually have to do a lexicographic
   * comparison rather than all the "not really" cases.
   * Here, m is the number of arguments we should consider (at least 2).
   * We let l = f(s1,...,sk) and r = g(t1,...,tn).
   */
  private void handleLexComplicated(FunctionSymbol f, FunctionSymbol g, int m, Term l, Term r,
                                    HorpoRequirement req) {
    // choose a parameter to decrease
    IVar index = _smt.createIntegerVariable();
    _smt.require(SmtFactory.createGeq(index, SmtFactory.createValue(1)));
    _smt.require(SmtFactory.createLeq(index, SmtFactory.createValue(m)));
    // for every i < index: either s_i ≈ t_i and both are regarded, or both are filtered
    for (int i = 1; i < m; i++) {
      Constraint igeqindex = SmtFactory.createGeq(SmtFactory.createValue(i), index);
      BVar fregards = _monotonicity.regards(f, i);
      BVar gregards = _monotonicity.regards(g, i);
      _smt.require(SmtFactory.createDisjunction(List.of(  // i < index ∧ f regarded => g too
        req.variable().negate(), igeqindex, fregards, gregards.negate())));
      _smt.require(SmtFactory.createDisjunction(List.of(  // i < index ∧ f disregarded => g too
        req.variable().negate(), igeqindex, fregards.negate(), gregards)));
      _smt.require(SmtFactory.createDisjunction(List.of(  // i < index ∧ f regarded => si ≈ t_i
        req.variable().negate(), igeqindex, fregards.negate(), _hcl.store(l.queryArgument(i),
          HRelation.GEQNOGR, r.queryArgument(i), req.constraint(), req.theoryVariables()))));
    }
    // s_{index} ≻ t_{index} and both are regarded
    for (int i = 1; i <= m; i++) {
      Constraint ineqindex = SmtFactory.createUnequal(SmtFactory.createValue(i), index);
      _smt.require(SmtFactory.createDisjunction(List.of(  // i = index => f regards i
        req.variable().negate(), ineqindex, _monotonicity.regards(f, i))));
      _smt.require(SmtFactory.createDisjunction(List.of(  // i = index => g regards i
        req.variable().negate(), ineqindex, _monotonicity.regards(g, i))));
      _smt.require(SmtFactory.createDisjunction(List.of(  // i = index => s_i ≻ t_i
        req.variable().negate(), ineqindex, _hcl.store(l.queryArgument(i), HRelation.GREATER,
          r.queryArgument(i), req.constraint(), req.theoryVariables()))));
    }
    // for every i: if t_i is regarded, then l ▷ t_i
    // (we ignore the first argument, because that is definitely covered by the lex requirements)
    requireLeftGreaterRightArguments(req, 2);
  }

  private void handleMul(HorpoRequirement req) {
    Term l = req.left();
    Term r = req.right();
    // TODO: we're being very minimalistic here, and only allowing Mul if both sides have the same
    // root; once we add support for different variables being compared, we should also require that
    // f _can_ take at least two arguments below (and/or: abort if we get the constant 1 from the
    // parameters as status(f))
    FunctionSymbol f = l.queryRoot();
    if (!r.isFunctionalTerm() || !r.queryRoot().equals(f) || r.numberArguments() <= 1 ||
        l.numberArguments() == 0) {
      _smt.require(req.variable().negate());
      return; 
    }
    FunctionSymbol g = r.queryRoot();
    int n = l.numberArguments(), m = r.numberArguments();
    if (n > m) n = m;
    // we let l = f l1 ... ln (perhaps with more arguments added, but these
    // cannot possibly contribute to the mul relation) and r = f r1 ... rm
    // note that m is at least 2; n may also be 1

    // to apply mul, status(f) should be Mul_k, which we represent as k > 1
    IntegerExpression status = _parameters.getStatusFor(f);
    handleMulBasics(req, status);
    TreeMap<Integer,TreeSet<Integer>> comparable = createComparable(l, n, r, m);
    TreeMap<Integer,BVar> strict = createStrict(req.variable(), f, status, n);
    TreeMap<Integer,IVar> pi = createProjection(req.variable(), f, status, n, m, comparable);
    requirePiEqualityForNonStrict(req.variable(), status, n, m, comparable, strict, pi);

    for (int i = 1; i <= m; i++) {
      Constraint itoobig = SmtFactory.createGreater(SmtFactory.createValue(i), status);
      TreeSet<Integer> ok = comparable.get(i);
      for (int j = 1; j <= n; j++) {
        if (!ok.contains(j)) continue;
        Constraint pinotj = SmtFactory.createUnequal(SmtFactory.createValue(j), pi.get(i));
        Constraint notstrict = SmtFactory.createNegation(strict.get(j));
        // if [req] ∧ i ≤ status ∧ π(i) = j ∧ strict_j then s_i > t_j
        BVar gr = _hcl.store(l.queryArgument(j), HRelation.GREATER, r.queryArgument(i),
                             req.constraint(), req.theoryVariables());
        Constraint c = SmtFactory.createDisjunction(
          SmtFactory.createDisjunction(itoobig, pinotj),
          SmtFactory.createDisjunction(notstrict, gr));
        _smt.requireImplication(req.variable(), c);
        // if [req] ∧ i ≤ status ∧ π(i) = j ∧ ¬strict_j then s_i ≥ t_j
        BVar geq = _hcl.store(l.queryArgument(j), HRelation.GEQ, r.queryArgument(i),
                              req.constraint(), req.theoryVariables());
        c = SmtFactory.createDisjunction(
          SmtFactory.createDisjunction(itoobig, pinotj),
          SmtFactory.createDisjunction(strict.get(j), geq));
        _smt.requireImplication(req.variable(), c);
      }
    }
  }

  /**
   * Given a requirement f l1...ln ▷{φ} f r1...rm by Rpo-mul, this adds the constraints that for
   * this requirement to hold, we need status(f) = Mul_k with k ≤ m, and that f l1...ln ▷{φ} for
   * all unfiltered ri where this is not already automatically implied by the multiset requirements
   */
  private void handleMulBasics(HorpoRequirement req, IntegerExpression status) {
    Term r = req.right();
    int m = r.numberArguments();

    // [req] → k > 1 (as k = 1 implies a Lex step)
    _smt.requireImplication(req.variable(), SmtFactory.createGreater(status,
        SmtFactory.createValue(1)));

    // [req] → k ≤ m (we only require this if f r1 ... rm does not have base type, since otherwise
    // it is already covered by the constraint on the creation of the status variable k)
    if (r.queryType().isArrowType()) {
      _smt.requireImplication(req.variable(),
        SmtFactory.createLeq(status, SmtFactory.createValue(m)));
    }

    // [req] → l ▷{φ} r_i for all arguments i; however, we omit 1,2 since the multiset constraints
    // always imply this (for i > 2, it could be that k = 2, and then these are not required)
    requireLeftGreaterRightArguments(req, 3);
  }

  /**
   * Given a requirement f l1...ln ▷{φ} f r1...rm by 1e, this returns which variables ri and lj can
   * be compared (typewise).
   */
  private TreeMap<Integer,TreeSet<Integer>> createComparable(Term left, int n, Term right, int m) {
    TreeMap<Integer,TreeSet<Integer>> ret = new TreeMap<Integer,TreeSet<Integer>>();
    for (int i = 1; i <= m; i++) {
      TreeSet<Integer> comp = new TreeSet<Integer>();
      for (int j = 1; j <= n; j++) {
        if (sameTypeStructure(left.queryArgument(j).queryType(),
                              right.queryArgument(i).queryType())) {
          comp.add(j);
        }
      }
      ret.put(i, comp);
    }
    return ret;
  }

  /**
   * Given a requirement f l1...ln ▷{φ} f r1...rm by 1e, this creates variables strict_1...strict_n
   * and (conditional on the main requirement holding) requires that at least one of those, which
   * is smaller than status and unfiltered, is true.
   */
  private TreeMap<Integer,BVar> createStrict(BVar reqvar, FunctionSymbol root,
                                             IntegerExpression status, int n) {
    TreeMap<Integer,BVar> ret = new TreeMap<Integer,BVar>();
    ArrayList<Constraint> oneof = new ArrayList<Constraint>();
    for (int j = 1; j <= n; j++) {
      BVar strict_j = _smt.createBooleanVariable();
      _smt.requireImplication(reqvar, SmtFactory.createDisjunction(strict_j.negate(),
        _monotonicity.regards(root, j)));
      ret.put(j, strict_j);
      oneof.add(strict_j);
      if (j > 2) {
        // [req] → ([strict_j] → k ≥ j)
        Constraint constr = SmtFactory.createImplication(strict_j,
          SmtFactory.createGeq(status, SmtFactory.createValue(j)));
        _smt.requireImplication(reqvar, constr);
      }
    }

    // [req] → [strict_1] ∨ ... ∨ [strict_n]
    _smt.requireImplication(reqvar, SmtFactory.createDisjunction(oneof));
    return ret;
  }

  /**
   * Given a requirement f l1...ln ▷{φ} f r1...rm by 1e, this creates variables π(i) ∈ {1..n}
   * for all i ∈ {1,..,m}.  It also adds the requirement that each unfiltered i ≤ status is
   * mapped to some unfiltered j ≤ status.
   */
  private TreeMap<Integer,IVar> createProjection(BVar reqvar, FunctionSymbol root, IntegerExpression
                              status, int n, int m, TreeMap<Integer,TreeSet<Integer>> comparable ) {
    // create variables π(i)
    TreeMap<Integer,IVar> pi = new TreeMap<Integer,IVar>();
    for (int i = 1; i <= m; i++) pi.put(i, _smt.createIntegerVariable());
    // require that, for 1 ≤ i ≤ status with i regarded
    // - 1 ≤ π(i) ≤ status
    // - π(i) ≤ n
    // - π(i) is regarded
    for (int i = 1; i <= m; i++) {
      IVar pi_i = pi.get(i);
      Constraint reqdoesnothold = reqvar.negate();
      Constraint idisregarded = _monotonicity.regards(root, i).negate();
      Constraint inotinrange = SmtFactory.createGreater(SmtFactory.createValue(i), status);
      Constraint irrelevant =
        SmtFactory.createDisjunction(List.of(reqdoesnothold, idisregarded, inotinrange));
      // 1 ≤ π(i)
      Constraint atleastone = SmtFactory.createGeq(pi_i, SmtFactory.createValue(1));
      _smt.require(SmtFactory.createDisjunction(irrelevant, atleastone));
      // π(i) ≤ status
      Constraint atmostk = SmtFactory.createLeq(pi_i, status);
      _smt.require(SmtFactory.createDisjunction(irrelevant, atmostk));
      // π(i) ≤ n
      Constraint atmostn = SmtFactory.createLeq(pi_i, SmtFactory.createValue(n));
      _smt.require(SmtFactory.createDisjunction(irrelevant, atmostn));
      // π(i) is regarded
      for (int j = 1; j <= n; j++) {
        // irrelevant OR π(i) != j OR j is regarded
        Constraint pi_i_not_j = SmtFactory.createUnequal(pi_i, SmtFactory.createValue(j));
        _smt.require(SmtFactory.createDisjunction(List.of(irrelevant, pi_i_not_j,
          _monotonicity.regards(root, j))));
      }
    }
    // require that π(i) != j if l_j and r_i do not have the same type structure
    for (int i = 1; i <= m; i++) {
      TreeSet<Integer> ok = comparable.get(i);
      IVar pi_i = pi.get(i);
      for (int j = 1; j <= n; j++) {
        if (!ok.contains(j)) {
          _smt.requireImplication(reqvar, SmtFactory.createUnequal(pi_i, SmtFactory.createValue(j)));
        }
      }
    }
    return pi;
  }

  private void requirePiEqualityForNonStrict(BVar reqvar, IntegerExpression status, int n, int m,
                                             TreeMap<Integer,TreeSet<Integer>> comparable,
                                             TreeMap<Integer,BVar> strict,
                                             TreeMap<Integer,IVar> pi) {
    // require that if π(i) = j ∧ pi(i') = j then strict_j
    for (int i1 = 1; i1 < m; i1++) {
      for (int i2 = i1+1; i2 <= m; i2++) {
        for (int j = 1; j <= n; j++) {
          if (!comparable.get(i1).contains(j)) continue;
          if (!comparable.get(i2).contains(j)) continue;
          // create: pi(i1) != j
          Constraint c1 = SmtFactory.createUnequal(pi.get(i1), SmtFactory.createValue(j));
          // create: pi(i2) != j
          Constraint c2 = SmtFactory.createUnequal(pi.get(i2), SmtFactory.createValue(j));
          // create: strict_j
          Constraint c3 = strict.get(j);
          // combine them
          Constraint d = SmtFactory.createDisjunction(SmtFactory.createDisjunction(c1, c2), c3);
          // and require for this clause to hold if req holds
          _smt.requireImplication(reqvar, d);
        }
      }
    }
  }
}
