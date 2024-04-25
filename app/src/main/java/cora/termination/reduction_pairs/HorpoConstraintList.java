/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination.reduction_pairs;

import java.util.List;
import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import charlie.types.*;
import charlie.terms.*;
import charlie.smt.*;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;

/**
 * The HorpoConstraintList is the core ingredient of the Horpo reduction pair.
 *
 * The HorpoConstraintList keeps track of a number of requirements, each indexed by a unique
 * "defining variable".  The HorpoConstraintList also keeps track of the HorpoParameters, including
 * an SmtProblem.
 *
 * To simplify the HorpoConstraintList, a requirement in the list (that hasn't yet been handled) is
 * expressed as an SMT formula over its defining variable, and the defining variables of simpler SMT
 * problems (e.g., for a requirement "f(x,y) ▷{select} r | φ" we store the constraint
 * [x ▷{select} r | φ] → [x ≽ r | φ] ∨ [y ≽ r | φ]).  The simpler SMT problems are also added to
 * the HorpoConstraintList and simplified in their turn, until the original list of ordering
 * requirements is reduced to an SMT problem whose satisfiability expresses:
 * FORALL initial inequality: IF <defining variable of that inequality> THEN that inequality holds.
 */
class HorpoConstraintList {
  /** Default only for the sake of unit testing */
  enum Relation { GREATER, GREATERTHEORY, GREATERMONO, GREATERARGS, GREATERRPO,
                  GEQ, GEQTHEORY, GEQEQUAL, GEQMONO, GEQARGS,
                  GEQNOGR, GEQNOGRTHEORY, GEQNOGREQUAL, GEQNOGRMONO, GEQNOGRARGS,
                  RPO, RPOSELECT, RPOAPPL, RPOCOPY, RPOLEX, RPOMUL, RPOTH };
  public enum StartRelation { Greater, Geq, GeqNoGr };

  /**
   * A HorpoRequirement models an inequality of the form left REL right | constraint, theorvar,
   * where theorval contains variables in left and/or right that may be assumed to be instantiated
   * by ground theory terms.
   * Note that this should include all variables in Var(left) ∪ Var(right) that also occur in
   * Var(constraint).
   */
  private record HorpoRequirement(Term left, Relation relation, Term right, Term constraint,
                                  TreeSet<Variable> theoryVariables, BVar variable) { }

  private final HorpoParameters _parameters;
  private SmtProblem _problem;
  private final TermPrinter _printer;
  private ArrayList<HorpoRequirement> _constraints;
  private int _handled;
  private TreeMap<String,BVar> _definingVariables;

  /**
   * Sets up a fresh list, with no requirements yet.
   *
   * The given HorpoParameters are used for simplifying the requirements, and for its SmtProblem
   * (which is used both to generate variables and to store defining formulas).
   *
   * The given TermPrinter is used to print the requirements, which is important internally since
   * it is used for requirements caching.  Hence, it is essential that two requiements cannot be
   * printed the same if they are actually different.  Thus, the caller should ensure that all the
   * function symbols that might occur in any requirement passed to the HorpoConstraintList are
   * registered as "avoid" symbols in the given printer.
   */
  public HorpoConstraintList(HorpoParameters parameters, TermPrinter printer) {
    _parameters = parameters;
    _printer = printer;
    _problem = parameters.queryProblem();

    _constraints = new ArrayList<HorpoRequirement>();
    _handled = 0;
    _definingVariables = new TreeMap<String,BVar>();
  }

  /**
   * Stores an inequality l REL r | phi, and returns the defining variable.
   *
   * Note: if the inequality is already in the constraint list, then nothing is stored, and the
   * corresponding defining variable is returned.  If the requirement is new, then it is indeed
   * stored and a new defining variable is created.
   */
  public BVar store(Term left, StartRelation rel, Term right, Term constraint) {
    Relation relation = switch (rel) {
      case StartRelation.Greater -> Relation.GREATER;
      case StartRelation.Geq -> Relation.GEQ;
      case StartRelation.GeqNoGr -> Relation.GEQNOGR;
    };
    TreeSet<Variable> constraintvars = new TreeSet<Variable>();
    for (Variable x : constraint.vars()) constraintvars.add(x);
    return getVariableFor(left, relation, right, constraint, constraintvars);
  }

  /**
   * Stores a requirement for the given inequality, and returns the defining variable.  The given
   * set of theory variables (variables that can be assumed to be instantiated only with ground
   * theory terms) should include all the variables in the constraint.
   *
   * Note: if the requirement is already in the constraint list, then nothing is stored, and the
   * corresponding defining variable is returned.  If the requirement is new, then it is indeed
   * stored and a new defining variable is created.
   */
  public BVar store(Term left, StartRelation rel, Term right, Term constraint, Set<Variable> tvar) {
    Relation relation = switch (rel) {
      case StartRelation.Greater -> Relation.GREATER;
      case StartRelation.Geq -> Relation.GEQ;
      case StartRelation.GeqNoGr -> Relation.GEQNOGR;
    };
    return getVariableFor(left, relation, right, constraint, new TreeSet<Variable>(tvar));
  }

  /**
   * Internal function handling the functionality of store, and which can also be used to store
   * all the relations, not just the outer ones.
   *
   * The given TreeSet is the property of HorpoConstraintList, but could be used as part of
   * another requirement so should not be modified.
   *
   * This is left default rather than private for the sake of unit testing.
   */
  BVar getVariableFor(Term left, Relation relation, Term right, Term constraint,
                      TreeSet<Variable> tvar) {
    // ensure that tvar only contains variables that occur in left or right
    TreeSet<Variable> myvars = new TreeSet<Variable>();
    for (Variable x : tvar) {
      if (left.vars().contains(x) || right.vars().contains(x)) myvars.add(x);
    }
    if (myvars.size() != tvar.size()) tvar = myvars;
    // find the defining variable, or create a new one (in which case the constraint is stored
    String representation = reqToString(left, relation, right, constraint, tvar);
    BVar ret = _definingVariables.get(representation);
    if (ret != null) return ret;
    ret = _problem.createBooleanVariable(representation);
    _definingVariables.put(representation, ret);
    HorpoRequirement req = new HorpoRequirement(left, relation, right, constraint, tvar, ret);
    _constraints.add(req);
    return ret;
  }

  /** Returns a string representation that uniquely identifies the given constraint */
  private String reqToString(Term left, Relation relation, Term right, Term constraint,
                             TreeSet<Variable> theorvar) {
    TermPrinter.Renaming naming = _printer.generateUniqueNaming(constraint, left, right);
    StringBuilder builder = new StringBuilder();
    _printer.print(left, naming, builder);
    builder.append(switch(relation) {
      case Relation.GREATER       -> " ≻ ";
      case Relation.GREATERTHEORY -> " ≻{theory} ";
      case Relation.GREATERMONO   -> " ≻{mono} ";
      case Relation.GREATERARGS   -> " ≻{args} ";
      case Relation.GREATERRPO    -> " ≻{rpo} ";
      case Relation.GEQ           -> " ≽ ";
      case Relation.GEQTHEORY     -> " ≽{theory} ";
      case Relation.GEQEQUAL      -> " ≽{equal} ";
      case Relation.GEQMONO       -> " ≽{mono} ";
      case Relation.GEQARGS       -> " ≽{args} ";
      case Relation.GEQNOGR       -> " ≈ ";
      case Relation.GEQNOGRTHEORY -> " ≈{theory} ";
      case Relation.GEQNOGREQUAL  -> " ≈{equal} ";
      case Relation.GEQNOGRMONO   -> " ≈{mono} ";
      case Relation.GEQNOGRARGS   -> " ≈{args} ";
      case Relation.RPO           -> " ▷ ";
      case Relation.RPOSELECT     -> " ▷{select} ";
      case Relation.RPOAPPL       -> " ▷{appl} ";
      case Relation.RPOCOPY       -> " ▷{copy} ";
      case Relation.RPOLEX        -> " ▷{lex} ";
      case Relation.RPOMUL        -> " ▷{mul} ";
      case Relation.RPOTH     -> " ▷{th} ";
    });
    _printer.print(right, naming, builder);
    builder.append(" | ");
    _printer.print(constraint, naming, builder);
    builder.append(" {");
    for (Variable v : theorvar) {
      builder.append(" ");
      _printer.print(v, naming, builder);
    }
    builder.append(" }");
    return builder.toString();
  }

  /**
   * Returns a string representation of all HorpoRequirements in the list (for debugging and unit
   * testing purposes).
   */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    for (int i = 0; i < _constraints.size(); i++) {
      if (i < _handled) builder.append("$ ");
      else builder.append("@ ");
      builder.append(_constraints.get(i).variable().queryName());
      builder.append("\n");
    }
    return builder.toString();
  }

  /**
   * Returns true if all the constraints in the list have been handled (that is, have their
   * defining clauses in the SmtProblem.
   */
  public boolean isFullySimplified() {
    return _handled >= _constraints.size();
  }

  /** This does a single simplification step, simplifying one HorpoRequirement in the list. */
  public void simplify() {
    if (_handled >= _constraints.size()) return;
    HorpoRequirement req = _constraints.get(_handled);
    _handled++;
    switch (req.relation) {
      case Relation.GREATER:       handleGreater(req); break;
      case Relation.GREATERTHEORY: handleTheory(req); break;
      case Relation.GREATERMONO:   handleGreaterMono(req); break;
      case Relation.GREATERARGS:   handleArgs(req); break;
      case Relation.GREATERRPO:    handleGreaterRpo(req); break;
      case Relation.GEQ:           handleGeq(req); break;
      case Relation.GEQTHEORY:     handleTheory(req); break;
      case Relation.GEQEQUAL:      handleEqual(req); break;
      case Relation.GEQMONO:       handleMono(req); break;
      case Relation.GEQARGS:       handleArgs(req); break;
      case Relation.GEQNOGR:       handleGeqNoGr(req); break;
      case Relation.GEQNOGRTHEORY: handleTheory(req); break;
      case Relation.GEQNOGREQUAL:  handleEqual(req); break;
      case Relation.GEQNOGRMONO:   handleMono(req); break;
      case Relation.GEQNOGRARGS:   handleArgs(req); break;
      case Relation.RPO:           handleRpo(req); break;
      case Relation.RPOSELECT:     handleSelect(req); break;
      case Relation.RPOAPPL:       handleAppl(req); break;
      case Relation.RPOCOPY:       handleCopy(req); break;
      case Relation.RPOLEX:        handleLex(req); break;
      case Relation.RPOMUL:        handleMul(req); break;
      case Relation.RPOTH:         handleRpoTheory(req); break;
    }
  }

  /**
   * Returns whether or not a and b are equal modulo renaming of base types.
   * Here, we treat product types as unequal to anything, even themselves, as the theory has not
   * yet been defined for product types.
   */
  private boolean sameTypeStructure(Type a, Type b) {
    return switch (a) {
      case Base(_) -> switch (b) {
        case Base _ -> true;
        case Arrow _, Product _ -> false;
      };
      case Arrow(Type in1, Type out1) -> switch (b) {
        case Base _, Product _ -> false;
        case Arrow(Type in2, Type out2) -> sameTypeStructure(in1, in2) && sameTypeStructure(out1, out2);
      };
      case Product _ -> false;
    };
  }

  /***********************************************************************************************/
  /* The functions below all serve to simplify different kinds of HorpoConstraints.              */
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
      _problem.require(req.variable.negate());
      return;
    }
    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    ArrayList<Constraint> lst = new ArrayList<Constraint>();
    // for theory terms, only Relation.GREATERTHEORY applies; for non-theory terms, only the
    // other options apply
    if (l.isTheoryTerm()) lst.add(getVariableFor(l, Relation.GREATERTHEORY, r, c, v));
    else {
      lst.add(getVariableFor(l, Relation.GREATERRPO, r, c, v));
      lst.add(getVariableFor(l, Relation.GREATERMONO, r, c, v));
      lst.add(getVariableFor(l, Relation.GREATERARGS, r, c, v));
    }
    Constraint combi = SmtFactory.createDisjunction(lst);
    _problem.requireImplication(req.variable, combi);
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
      _problem.require(req.variable.negate());
      return;
    }
    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    ArrayList<Constraint> lst = new ArrayList<Constraint>();
    // for theory terms, only GEQTHEORY and GEQEQUAL apply; for non-theory terms, only the other
    // options apply
    if (l.isTheoryTerm()) {
      lst.add(getVariableFor(l, Relation.GEQTHEORY, r, c, v));
      lst.add(getVariableFor(l, Relation.GEQEQUAL, r, c, v));
    }
    else {
      lst.add(getVariableFor(l, Relation.GREATERRPO, r, c, v));
      lst.add(getVariableFor(l, Relation.GEQMONO, r, c, v));
      lst.add(getVariableFor(l, Relation.GEQARGS, r, c, v));
    }
    Constraint combi = SmtFactory.createDisjunction(lst);
    _problem.requireImplication(req.variable, combi);
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
      _problem.require(req.variable.negate());
      return;
    }
    Term c = req.constraint();
    TreeSet<Variable> v = req.theoryVariables();
    ArrayList<Constraint> lst = new ArrayList<Constraint>();
    // for theory terms, only GEQTHEORY and GEQEQUAL apply; for non-theory terms, only the other
    // options apply
    if (l.isTheoryTerm()) {
      lst.add(getVariableFor(l, Relation.GEQNOGRTHEORY, r, c, v));
      lst.add(getVariableFor(l, Relation.GEQNOGREQUAL, r, c, v));
    }
    else {
      lst.add(getVariableFor(l, Relation.GEQNOGRMONO, r, c, v));
      lst.add(getVariableFor(l, Relation.GEQNOGRARGS, r, c, v));
    }
    Constraint combi = SmtFactory.createDisjunction(lst);
    _problem.requireImplication(req.variable, combi);
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
    ArrayList<Constraint> lst = new ArrayList<Constraint>();
    lst.add(getVariableFor(l, Relation.RPOTH, r, c, v));
    lst.add(getVariableFor(l, Relation.RPOSELECT, r, c, v));
    lst.add(getVariableFor(l, Relation.RPOCOPY, r, c, v));
    lst.add(getVariableFor(l, Relation.RPOLEX, r, c, v));
    lst.add(getVariableFor(l, Relation.RPOMUL, r, c, v));
    lst.add(getVariableFor(l, Relation.RPOAPPL, r, c, v));
    Constraint combi = SmtFactory.createDisjunction(lst);
    _problem.requireImplication(req.variable, combi);
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
    Relation relation = req.relation();
    if (!theoryAllowed(l, r, v)) _problem.require(variable.negate());
    else if (relation == Relation.GEQNOGRTHEORY) {
      BVar x = getVariableFor(l, Relation.GEQTHEORY, r, phi, v);
      BVar y = getVariableFor(l, Relation.GREATERTHEORY, r, phi, v);
      _problem.require(SmtFactory.createIff(variable, SmtFactory.createConjunction(x, y.negate())));
    }
    else if (l.queryType().equals(TypeFactory.intSort)) {
      handleIntComparison(l, r, phi, variable, relation);
    }
    else if (l.queryType().equals(TypeFactory.boolSort)) {
      handleBoolComparison(l, r, phi, variable, relation);
    }
    else _problem.require(variable.negate());
  }

  /** Returns whether we are even allowed to apply one of the theory cases */
  private boolean theoryAllowed(Term l, Term r, Set<Variable> theoryVariables) {
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
  private void handleIntComparison(Term l, Term r, Term phi, BVar x, Relation rel) {
    SmtProblem validityProblem = new SmtProblem();
    TermSmtTranslator tst = new TermSmtTranslator(validityProblem);
    IntegerExpression el = tst.translateIntegerExpression(l);
    IntegerExpression er = tst.translateIntegerExpression(r);
    Constraint c = tst.translateConstraint(phi);

    Constraint downProblem, upProblem;
    if (rel == Relation.GREATERTHEORY) {
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

    if (downValid && upValid) _problem.require(x);
    else if (downValid) {
      _problem.require(SmtFactory.createIff(x, _parameters.getDirectionIsDownVariable()));
    }
    else if (upValid) {
      _problem.require(SmtFactory.createIff(x, _parameters.getDirectionIsDownVariable().negate()));
    }
    else _problem.require(x.negate());
  }

  /**
   * For boolean comparisons, we fix true ⊐ false (as this case rarely occurs anyway).
   * Thus, we check if left ∧ ¬right (for strict comparison) or left ∨ ¬right (for weak comparison)
   * is valid, and force the value of x accordingly, so that x <--> left <rel> right.
   *
   * We use a separate SMT problem to do the validity check, as it should not be a part of the
   * satisfiability problem.
   */
  private void handleBoolComparison(Term l, Term r, Term phi, BVar x, Relation rel) {
    SmtProblem validityProblem = new SmtProblem();
    TermSmtTranslator tst = new TermSmtTranslator(validityProblem);
    Constraint cl = tst.translateConstraint(l);
    Constraint cr = tst.translateConstraint(r);
    Constraint cp = tst.translateConstraint(phi);
    Constraint negr = SmtFactory.createNegation(cr);

    Constraint constr;
    if (rel == Relation.GREATERTHEORY) constr = SmtFactory.createConjunction(cl, negr);
    else constr = SmtFactory.createDisjunction(cl, negr);
    validityProblem.requireImplication(cp, constr);

    if (Settings.smtSolver.checkValidity(validityProblem)) _problem.require(x);
    else _problem.require(x.negate());
  }

  private void handleEqual(HorpoRequirement req) {
    if (req.left.equals(req.right)) _problem.require(req.variable);
    else _problem.require(req.variable.negate());
  }

  /**
   * For now, this method simply adds a constraint that the given requirement is not satisfied.
   * In the future, this may be used for NON-FILTERING reduction pairs to allow a strict decrease
   * in a varterm.
   * TODO
   */
  private void handleGreaterMono(HorpoRequirement req) {
    _problem.require(req.variable.negate());
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
    Term left = req.left;
    Term right = req.right;

    if (!left.isVarTerm() || left.numberArguments() != right.numberArguments() ||
        !left.queryHead().equals(right.queryHead())) {
      _problem.require(req.variable.negate());
      return;
    }

    Relation subrel = req.relation == Relation.GEQNOGRMONO ? Relation.GEQNOGR : Relation.GEQ;
    for (int i = 1; i <= left.numberArguments(); i++) {
      BVar x = getVariableFor(left.queryArgument(i), subrel, right.queryArgument(i),
                              req.constraint, req.theoryVariables);
      _problem.requireImplication(req.variable, x);
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
    Term left = req.left;
    Term right = req.right;

    if (!left.isFunctionalTerm() || left.numberArguments() != right.numberArguments() ||
        !left.queryHead().equals(right.queryHead())) {
      _problem.require(req.variable.negate());
      return;
    }

    Relation subrel = req.relation == Relation.GEQNOGRARGS ? Relation.GEQNOGR : Relation.GEQ;
    FunctionSymbol f = left.queryRoot();
    for (int i = 1; i <= left.numberArguments(); i++) {
      BVar x = getVariableFor(left.queryArgument(i), subrel, right.queryArgument(i),
                              req.constraint, req.theoryVariables);
      BVar regards = _parameters.getRegardsVariableFor(f, i);
      _problem.requireImplication(req.variable, SmtFactory.createDisjunction(
        regards.negate(), x));
    }

    if (req.relation == Relation.GREATERARGS) {
      ArrayList<Constraint> onestrict = new ArrayList<Constraint>();
      for (int i = 1; i <= left.numberArguments(); i++) {
        BVar x = getVariableFor(left.queryArgument(i), Relation.GREATER, right.queryArgument(i),
                                req.constraint, req.theoryVariables);
        BVar regards = _parameters.getRegardsVariableFor(f, i);
        onestrict.add(SmtFactory.createConjunction(regards, x));
      }
      _problem.requireImplication(req.variable, SmtFactory.createDisjunction(onestrict));
    }
  }

  /**
   * This simplifies requirements of the form l ≻{rpo} r | φ by delegating to ▷ -- provided
   * the requirement satisfies the conditions to be used in ▷.
   */
  private void handleGreaterRpo(HorpoRequirement req) {
    if (!req.left.isFunctionalTerm() || req.left.isTheoryTerm()) {
      _problem.require(req.variable.negate());
    }
    else {
      if (req.left.queryType().isArrowType()) {
        FunctionSymbol f = req.left.queryRoot();
        int m = f.queryArity();
        for (int i = req.left.numberArguments() + 1; i <= m; i++) {
          _problem.requireImplication(req.variable, _parameters.getRegardsVariableFor(f, i));
        }
      }
      BVar x = getVariableFor(req.left,Relation.RPO,req.right,req.constraint,req.theoryVariables);
      _problem.requireImplication(req.variable, x);
    }
  }

  private void handleSelect(HorpoRequirement req) {
    Term l = req.left;
    FunctionSymbol f = l.queryRoot();
    ArrayList<Constraint> args = new ArrayList<Constraint>();
    for (int i = 1; i <= l.numberArguments(); i++) {
      BVar x = _parameters.getRegardsVariableFor(f, i);
      Term a = l.queryArgument(i);
      BVar y = getVariableFor(a, Relation.GEQ, req.right, req.constraint, req.theoryVariables);
      args.add(SmtFactory.createConjunction(x, y));
    }

    if (args.size() == 0) { _problem.require(req.variable.negate()); return; }
    else _problem.requireImplication(req.variable, SmtFactory.createDisjunction(args));
  }

  private void handleAppl(HorpoRequirement req) {
    Term r = req.right;
    if (r.numberArguments() == 0) {
      _problem.require(req.variable.negate());
      return;
    }
    Term a = r.queryImmediateHeadSubterm(r.numberArguments()-1);
    Term b = r.queryArgument(r.numberArguments());
    _problem.requireImplication(req.variable,
      getVariableFor(req.left, Relation.RPO, a, req.constraint, req.theoryVariables));
    _problem.requireImplication(req.variable,
      getVariableFor(req.left, Relation.RPO, b, req.constraint, req.theoryVariables));
  }

  /**
   * Helper function: this requires that req.left ▷ t_i for every regarded argument t_i of
   * req.right.  Here, req.right is required to be a functional term.
   */
  private void requireLeftGreaterRightArguments(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    FunctionSymbol g = r.queryRoot();
    for (int i = 1; i <= r.numberArguments(); i++) {
      BVar subreq = getVariableFor(l, Relation.RPO, r.queryArgument(i), req.constraint,
                                   req.theoryVariables);
      BVar regards = _parameters.getRegardsVariableFor(g, i);
      _problem.requireImplication(req.variable,
        SmtFactory.createDisjunction(regards.negate(), subreq));
    }
  }

  private void handleCopy(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    FunctionSymbol f = l.queryRoot();
    if (!r.isFunctionalTerm() || r.queryRoot().equals(f) || r.isValue()) {
      // values are excluded here because this case is already covered by thterm
      _problem.require(req.variable.negate());
    }
    else {
      FunctionSymbol g = r.queryRoot();
      IVar predf = _parameters.getPrecedenceFor(f);
      IVar predg = _parameters.getPrecedenceFor(g);
      _problem.requireImplication(req.variable, SmtFactory.createGreater(predf, predg));
      requireLeftGreaterRightArguments(req);
    }
  }

  private void handleLex(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    if (!l.isFunctionalTerm() || !r.isFunctionalTerm()) {
      _problem.require(req.variable.negate());
      return; 
    }
    FunctionSymbol f = l.queryRoot();
    FunctionSymbol g = r.queryRoot();
    // get the maximum relevant number of arguments; this should be at least 1
    int m = l.numberArguments();
    if (r.numberArguments() < m) m = r.numberArguments();
    if (m == 0) { _problem.require(req.variable.negate()); return; }
    // to apply lex, both function symbols should have the same status
    _problem.requireImplication(req.variable,
      SmtFactory.createEqual(_parameters.getPrecedenceFor(f), _parameters.getPrecedenceFor(g)));
    // moreover, they should both have Lex status
    _problem.requireImplication(req.variable,
      SmtFactory.createEqual(_parameters.getStatusFor(f), SmtFactory.createValue(1)));
    _problem.requireImplication(req.variable,
      SmtFactory.createEqual(_parameters.getStatusFor(g), SmtFactory.createValue(1)));
    // if there is only one argument, the decrease should be there
    if (m == 1) {
      _problem.requireImplication(req.variable, _parameters.getRegardsVariableFor(f, 1));
      _problem.requireImplication(req.variable, _parameters.getRegardsVariableFor(g, 1));
      _problem.requireImplication(req.variable,
        getVariableFor(l.queryArgument(1), Relation.GREATER, r.queryArgument(1),
                       req.constraint, req.theoryVariables));
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
    IVar index = _problem.createIntegerVariable();
    _problem.require(SmtFactory.createGeq(index, SmtFactory.createValue(1)));
    _problem.require(SmtFactory.createLeq(index, SmtFactory.createValue(m)));
    // for every i < index: either s_i ≈ t_i and both are regarded, or both are filtered
    for (int i = 1; i < m; i++) {
      Constraint igeqindex = SmtFactory.createGeq(SmtFactory.createValue(i), index);
      BVar fregards = _parameters.getRegardsVariableFor(f, i);
      BVar gregards = _parameters.getRegardsVariableFor(g, i);
      _problem.require(SmtFactory.createDisjunction(List.of(  // i < index ∧ f regarded => g too
        req.variable.negate(), igeqindex, fregards, gregards.negate())));
      _problem.require(SmtFactory.createDisjunction(List.of(  // i < index ∧ f disregarded => g too
        req.variable.negate(), igeqindex, fregards.negate(), gregards)));
      _problem.require(SmtFactory.createDisjunction(List.of(  // i < index ∧ f regarded => si ≈ t_i
        req.variable.negate(), igeqindex, fregards.negate(), getVariableFor(l.queryArgument(i),
          Relation.GEQNOGR, r.queryArgument(i), req.constraint, req.theoryVariables))));
    }
    // s_{index} ≻ t_{index} and both are regarded
    for (int i = 1; i <= m; i++) {
      Constraint ineqindex = SmtFactory.createUnequal(SmtFactory.createValue(i), index);
      _problem.require(SmtFactory.createDisjunction(List.of(  // i = index => f regards i
        req.variable.negate(), ineqindex, _parameters.getRegardsVariableFor(f, i))));
      _problem.require(SmtFactory.createDisjunction(List.of(  // i = index => g regards i
        req.variable.negate(), ineqindex, _parameters.getRegardsVariableFor(g, i))));
      _problem.require(SmtFactory.createDisjunction(List.of(  // i = index => s_i ≻ t_i
        req.variable.negate(), ineqindex, getVariableFor(l.queryArgument(i), Relation.GREATER,
          r.queryArgument(i), req.constraint, req.theoryVariables))));
    }
    // for every i: if t_i is regarded, then l ▷ t_i
    requireLeftGreaterRightArguments(req);
  }

  private void handleMul(HorpoRequirement req) {
    // TODO
    _problem.require(req.variable.negate());
  }

  /**
   * This function sets the defining variable of req to true if the right-hand side of req is a
   * theory term with all its variables in the theory variables of req, and to false otherwise.
   */
  private void handleRpoTheory(HorpoRequirement req) {
    Term r = req.right;
    boolean isgood = r.isTheoryTerm();
    if (isgood) {
      for (Variable x : r.vars()) {
        if (!req.theoryVariables.contains(x)) { isgood = false; break; }
      }
    }
    if (isgood) _problem.require(req.variable);
    else _problem.require(req.variable.negate());
  }
}

