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

package cora.termination.horpo;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.TreeMap;
import java.util.TreeSet;
import charlie.types.*;
import charlie.terms.*;
import charlie.smt.*;
import charlie.trs.*;
import charlie.trs.TrsProperties.*;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;

/**
 * This is an implementation of a basic version of Horpo for LCSTRSs (so with constraints).
 */
public class Horpo {
  /**
   * This function returns whether this termination analyser can be applied to the given TRS.
   * This is the case if it's an LCSTRS: an applicative constrained system where left-hand sides
   * are not theory terms.
   */
  private static boolean applicable(TRS trs) {
    return trs.verifyProperties(Level.APPLICATIVE, Constrained.YES, Products.DISALLOWED,
                                Lhs.NONPATTERN, Root.ANY);
  }

  /**
   * Given a TRS, this checks if it can be proved terminating using Horpo, and if so, returns a
   * HorpoResult describing the Horpo proof.  If not, null is returned instead.  (In this case
   * the termination couldn't be proved; we cannot conclude non-termination from this.)
   */
  public static HorpoResult run(TRS trs) {
    if (!applicable(trs)) {
      return new HorpoResult("The current implementation of HORPO can only be applied on " +
                             "systems with applicative term formation and no tuples.");
    }
    Horpo horpo = new Horpo(trs);
    while (horpo.handleTodo());
    return horpo.solve();
  }

  /***********************************************************************************************/
  /* An instance of HORPO keeps track of:                                                        */
  /* - a list of requirements <left rel{constraint} right>, each with a corresponding boolean    */
  /*   variable; this list is split up into:                                                     */
  /*   + the requirements for which we have already added a formula to the smt problem           */
  /*   + a list of requirements that we still need to handle                                     */
  /* - an SmtProblem representing the list of implications var → constraint that we need to      */
  /*   satisfy for the requirements to be satisfied                                              */
  /* - a mapping of requirement string → variable, so we don't add the same formulas multiple    */
  /*   times                                                                                     */
  /***********************************************************************************************/

  private static final int GREATER = 1;
  private static final int GEQ = 2;
  private static final int RPO = 3;
  private final SmtProblem _problem;
  private final TreeMap<String,IVar> _precedence;
  private final TreeMap<String,IVar> _status;
  private final LinkedList<HorpoRequirement> _todo;
  private final TreeMap<String,BVar> _varCache;
  private final BVar _down;
  private int _M;

  class HorpoRequirement {
    final Term left;
    final Term right;
    final Term constraint;
    final int relation; // one of GREATER, GEQ or RPO
    final int rule;
    final String clause;
    final BVar variable;
  
    HorpoRequirement(int rl, Term l, int rel, Term r, Term c, String cl, BVar x) {
      left = l;
      right = r;
      constraint = c;
      relation = rel;
      rule = rl;
      clause = cl;
      variable = x;
    }

    public String toString() {
      return variable.toString() + " => " +
             reqToString(rule, left, relation, right, constraint, clause);
    }
  }

  /** Default only for the sake of unit testing; this should be created by the static functions. */
  Horpo(TRS trs) {
    _problem = new SmtProblem();
    _todo = new LinkedList<HorpoRequirement>();
    _varCache = new TreeMap<String,BVar>();
    _precedence = new TreeMap<String,IVar>();
    _status = new TreeMap<String,IVar>();
    _down = _problem.createBooleanVariable();

    computeIntegerVariableBound(trs);

    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rule = trs.queryRule(i);
      Term left = rule.queryLeftSide(), right = rule.queryRightSide();
      Term constraint = fixConstraint(left, right, rule.queryConstraint());
      _problem.require(getVariableFor(i, left, GREATER, right, constraint, null));
    }
  }

  /**
   * We set M to twice the largest integer value occurring in the program (or just to 1000 if that
   * is bigger).
   */
  private void computeIntegerVariableBound(TRS trs) {
    _M = 500;
    LinkedList<Term> parts = new LinkedList<Term>();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rule = trs.queryRule(i);
      parts.push(rule.queryLeftSide());
      parts.push(rule.queryRightSide());
      parts.push(rule.queryConstraint());
    }
    while (!parts.isEmpty()) {
      Term part = parts.pop();
      if (part.isValue() && part.queryType().equals(TypeFactory.intSort)) {
        Value value = part.toValue();
        if (value.getInt() > _M) _M = value.getInt();
        if (- value.getInt() > _M) _M = - value.getInt();
      }
      if (part.isApplication()) {
        for (int i = 1; i <= part.numberArguments(); i++) parts.push(part.queryArgument(i));
      }
    }
    _M *= 2;
  }

  /**
   * Returns the precedence variable for a symbol f, creating it first if necessary.
   * Default for the sake of unit testing, but otherwise private.
   */
  IVar getPrecedenceFor(FunctionSymbol f) {
    if (_precedence.containsKey(f.toString())) return _precedence.get(f.toString());
    IVar x = _problem.createIntegerVariable();
    // theory symbols have values < 0, non-theory symbols ≥ 0
    if (f.isTheorySymbol()) _problem.require(SmtFactory.createSmaller(x, SmtFactory.createValue(0)));
    else _problem.require(SmtFactory.createGeq(x, SmtFactory.createValue(0)));
    _precedence.put(f.toString(), x);
    return x;
  }

  /**
   * Returns the status variable for a symbol f, creating it first if necessary.
   * We only create status variables for symbols with arity > 1; anything else automatically gets
   * lex (in which case null is returned).  The status is either 1 (for Lex), or i for m_i.
   * Default for the sake of unit testing, but otherwise private.
   */
  IVar getStatusFor(FunctionSymbol f) {
    if (f.queryArity() <= 1) return null;
    if (_status.containsKey(f.toString())) return _status.get(f.toString());
    IVar x = _problem.createIntegerVariable();
    _status.put(f.toString(), x);
    _problem.require(SmtFactory.createGeq(x, SmtFactory.createValue(1)));
    _problem.require(SmtFactory.createLeq(x, SmtFactory.createValue(f.queryArity())));
    return x;
  }

  /** We add variables from FV(right) \ FV(left) into the given constraint. */
  private Term fixConstraint(Term left, Term right, Term constraint) {
    Environment<Variable> lvars = left.vars();
    Environment<Variable> rvars = right.vars();
    Environment<Variable> cvars = constraint.vars();
    for (Variable x : rvars) {
      if (lvars.contains(x)) continue;
      if (cvars.contains(x)) continue;
      constraint = TermFactory.createApp(TheoryFactory.andSymbol, constraint,
        TermFactory.createApp(TheoryFactory.equalSymbol, x, x));
    }
    return constraint;
  }

  /**
   * To be able to recognise repeated occurrences of the same requirement left rel{constr} right,
   * we print them to string, and cache the requirements based on their string representation.
   */
  private String reqToString(int rule, Term left, int rel, Term right, Term constraint,
                             String clause) {
    StringBuilder ret = new StringBuilder();
    ret.append("" + rule + ": ");
    ret.append(left.toString());
    if (rel == GREATER) ret.append(" ≻");
    if (rel == GEQ) ret.append(" ≽");
    if (rel == RPO) ret.append(" ▷");
    ret.append("{");
    ret.append(constraint.toString());
    ret.append("} ");
    ret.append(right.toString());
    if (clause != null) ret.append(" by " + clause);
    return ret.toString();
  }

  /**
   * We find the unique variable associated to the given requirement.  If it was used before, this
   * comes from the cache; otherwise we generate a new variable and put the requirement to define
   * it into the _todo list.
   */
  private BVar getVariableFor(int rule, Term left, int rel, Term right, Term constraint,
                              String clause) {
    String str = reqToString(rule, left, rel, right, constraint, clause);
    BVar ret =  _varCache.get(str);
    if (ret != null) return ret;
    ret = _problem.createBooleanVariable();
    _varCache.put(str, ret);
    HorpoRequirement req = new HorpoRequirement(rule, left, rel, right, constraint, clause, ret);
    _todo.add(req);
    return ret;
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

  /**
   * This function takes a single item from the _todo list, and handles it, potentially adding more
   * todo items in the process.  If there are no _todo items left, then false is returned.
   *
   * Default rather than private only for the sake of unit testing.
   */
  boolean handleTodo() {
    if (_todo.isEmpty()) return false;
    HorpoRequirement req = _todo.pop();
    if (req.relation == GREATER) handleGreater(req);
    else if (req.relation == GEQ) handleGeq(req);
    else handleRpo(req);
    return true;
  }

  private void handleGeq(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    Term c = req.constraint;

    if (req.clause == null) {
      ArrayList<Constraint> lst = new ArrayList<Constraint>();
      lst.add(getVariableFor(req.rule, l, GEQ, r, c, "1c"));
      lst.add(getVariableFor(req.rule, l, GEQ, r, c, "1a"));
      lst.add(getVariableFor(req.rule, l, GEQ, r, c, "1b"));
      lst.add(getVariableFor(req.rule, l, GEQ, r, c, "1d"));
      Constraint combi = SmtFactory.createDisjunction(lst);
      _problem.requireImplication(req.variable, combi);
    }
    else if (req.clause.equals("1a")) {
      handleTheoryComparison(req.left, req.right, req.constraint, req.variable, false);
    }
    else if (req.clause.equals("1b")) handleGeqB(req);
    else if (req.clause.equals("1c")) handleGeqC(req);
    else if (req.clause.equals("1d")) handleGeqD(req);
  }

  /** Returns whether we are even allowed to apply case 1a or 2a */
  private boolean theoryAllowed(Term l, Term r, Term phi) {
    if (!l.isTheoryTerm() || !r.isTheoryTerm() || !l.queryType().isBaseType() ||
        !l.queryType().isTheoryType() || !l.queryType().equals(r.queryType())) {
      return false;
    }
    ReplaceableList lvars = l.freeReplaceables();
    ReplaceableList rvars = r.freeReplaceables();
    ReplaceableList cvars = phi.freeReplaceables();
    for (Replaceable x : lvars) if (!cvars.contains(x)) return false;
    for (Replaceable x : rvars) if (!cvars.contains(x)) return false;
    return true;
  }

  /**
   * To handle an integer comparison, we check whether φ → l > -M ∧ l > r is valid, and if not,
   * require that variable ∧ countDown cannot both hold; then we check the same for φ → l < M ∧
   * l < r and if not, require that variable ∧ ¬countDown cannot both hold.  If strict = false,
   * we also allow the option l = r in both cases.
   * We use a separate SMT problem to do the validity check, as it should not be a part of the
   * satisfiability problem.
   */
  private void handleIntComparison(Term l, Term r, Term phi, BVar variable, boolean strict) {
    SmtProblem validityProblem = new SmtProblem();
    TermSmtTranslator tst = new TermSmtTranslator(validityProblem);
    IntegerExpression el = tst.translateIntegerExpression(l);
    IntegerExpression er = tst.translateIntegerExpression(r);
    Constraint c = tst.translateConstraint(phi);
    Constraint equal = SmtFactory.createEqual(el, er);

    IntegerExpression eMM = SmtFactory.createValue(-_M);
    Constraint decrease = SmtFactory.createConjunction(  // l > -M ∧ l > r
      SmtFactory.createGreater(el, eMM),
      SmtFactory.createGreater(el, er));
    if (!strict) decrease = SmtFactory.createDisjunction(equal, decrease);  // l = r ∨ above
    validityProblem.requireImplication(c, decrease);
    if (!Settings.smtSolver.checkValidity(validityProblem)) {
      _problem.requireImplication(variable, SmtFactory.createNegation(_down));
    }

    validityProblem.clear();
    IntegerExpression eM = SmtFactory.createValue(_M);
    Constraint increase = SmtFactory.createConjunction(  // l < M ∧ l < r
      SmtFactory.createSmaller(el, eM),
      SmtFactory.createSmaller(el, er));
    if (!strict) increase = SmtFactory.createDisjunction(equal, increase);
    validityProblem.requireImplication(c, increase);
    if (!Settings.smtSolver.checkValidity(validityProblem)) {
      _problem.requireImplication(variable, _down);
    }
  }

  private void handleBoolComparison(Term l, Term r, Term phi, BVar variable, boolean strict) {
    SmtProblem validityProblem = new SmtProblem();
    TermSmtTranslator tst = new TermSmtTranslator(validityProblem);
    Constraint cl = tst.translateConstraint(l);
    Constraint cr = tst.translateConstraint(r);
    Constraint cp = tst.translateConstraint(phi);
    Constraint negr = SmtFactory.createNegation(cr);

    // we fix the comparison true ⊐ false (as this case rarely occurs anyway)
    Constraint constr;
    if (strict) constr = SmtFactory.createConjunction(cl, negr);
    else constr = SmtFactory.createDisjunction(cl, negr);
    validityProblem.requireImplication(cp, constr);

    if (!Settings.smtSolver.checkValidity(validityProblem)) {
      _problem.require(SmtFactory.createNegation(variable));
    }
  }

  private void handleTheoryComparison(Term l, Term r, Term phi, BVar variable, boolean strict) {
    if (!theoryAllowed(l, r, phi)) _problem.require(SmtFactory.createNegation(variable));
    else if (l.queryType().equals(TypeFactory.intSort)) {
      handleIntComparison(l, r, phi, variable, strict);
    }
    else if (l.queryType().equals(TypeFactory.boolSort)) {
      handleBoolComparison(l, r, phi, variable, strict);
    }
    else _problem.require(SmtFactory.createNegation(variable));
  }

  private void handleGeqB(HorpoRequirement req) {
    // for theory terms, > never succeeds where the other rules for ≥ fail
    if (req.left.isTheoryTerm()) _problem.require(SmtFactory.createNegation(req.variable));
    else {
       BVar x = getVariableFor(req.rule, req.left, GREATER, req.right, req.constraint, null);
      _problem.requireImplication(req.variable, x);
    }
  }

  private void handleGeqC(HorpoRequirement req) {
    // this case is actually only relevant if both sides are equal: if they are theory terms we
    // have l ≥ r by 1a, and if they are applications we have l ≥ r by 1d
    if (!req.left.equals(req.right)) _problem.require(SmtFactory.createNegation(req.variable));
  }

  private void handleGeqD(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    if (l.isApplication() && r.isApplication()) {
      Term la = l.queryImmediateHeadSubterm(l.numberArguments()-1);
      Term lb = l.queryArgument(l.numberArguments());
      Term ra = r.queryImmediateHeadSubterm(r.numberArguments()-1);
      Term rb = r.queryArgument(r.numberArguments());
      if (sameTypeStructure(lb.queryType(), rb.queryType())) {
        BVar x = getVariableFor(req.rule, la, GEQ, ra, req.constraint, null);
        BVar y = getVariableFor(req.rule, lb, GEQ, rb, req.constraint, null);
        _problem.requireImplication(req.variable, x);
        _problem.requireImplication(req.variable, y);
        return;
      }
    }
    _problem.require(SmtFactory.createNegation(req.variable));
  }

  private void handleGreater(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    Term c = req.constraint;

    if (req.clause == null) {
      ArrayList<Constraint> lst = new ArrayList<Constraint>();
      lst.add(getVariableFor(req.rule, l, GREATER, r, c, "2a"));
      lst.add(getVariableFor(req.rule, l, GREATER, r, c, "2c"));
      lst.add(getVariableFor(req.rule, l, GREATER, r, c, "2d"));
      lst.add(getVariableFor(req.rule, l, GREATER, r, c, "2b"));
      Constraint combi = SmtFactory.createDisjunction(lst);
      _problem.requireImplication(req.variable, combi);
    }
    else if (req.clause.equals("2a")) {
      handleTheoryComparison(req.left, req.right, req.constraint, req.variable, true);
    }
    else if (req.clause.equals("2b")) handleGreaterB(req);
    else if (req.clause.equals("2c")) handleGreaterC(req);
    else if (req.clause.equals("2d")) handleGreaterD(req);
  }

  private void handleGreaterB(HorpoRequirement req) {
    if (!req.left.isFunctionalTerm() || req.left.isTheoryTerm()) {
      _problem.require(SmtFactory.createNegation(req.variable));
    }
    else {
      BVar x = getVariableFor(req.rule, req.left, RPO, req.right, req.constraint, null);
      _problem.requireImplication(req.variable, x);
    }
  }

  private void handleGreaterArguments(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    ArrayList<Constraint> onestrict = new ArrayList<Constraint>();
    for (int i = 1; i <= l.numberArguments(); i++) {
      BVar x = getVariableFor(req.rule, l.queryArgument(i), GEQ, r.queryArgument(i),
                              req.constraint, null);
      _problem.requireImplication(req.variable, x);
      onestrict.add(getVariableFor(req.rule, l.queryArgument(i), GREATER, r.queryArgument(i),
                                   req.constraint, null));
    }
    _problem.requireImplication(req.variable, SmtFactory.createDisjunction(onestrict));
  }

  private void handleGreaterC(HorpoRequirement req) {
    if (!req.left.isFunctionalTerm() || !req.right.isFunctionalTerm() ||
        req.left.numberArguments() != req.right.numberArguments() ||
        !req.left.queryRoot().equals(req.right.queryRoot())) {
      _problem.require(SmtFactory.createNegation(req.variable));
    }
    else handleGreaterArguments(req);
  }

  private void handleGreaterD(HorpoRequirement req) {
    if (!req.left.isVarTerm() || !req.right.isVarTerm() ||
        req.left.numberArguments() != req.right.numberArguments() ||
        !req.left.queryVariable().equals(req.right.queryVariable())) {
      _problem.require(SmtFactory.createNegation(req.variable));
    }
    else handleGreaterArguments(req);
  }

  private void handleRpo(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    Term c = req.constraint;
    FunctionSymbol f = l.queryRoot();

    if (req.clause == null) {
      ArrayList<Constraint> combi = new ArrayList<Constraint>();
      combi.add(getVariableFor(req.rule, l, RPO, r, c, "3f"));
      combi.add(getVariableFor(req.rule, l, RPO, r, c, "3a"));
      combi.add(getVariableFor(req.rule, l, RPO, r, c, "3c"));
      combi.add(getVariableFor(req.rule, l, RPO, r, c, "3d"));
      combi.add(getVariableFor(req.rule, l, RPO, r, c, "3e"));
      combi.add(getVariableFor(req.rule, l, RPO, r, c, "3b"));
      _problem.requireImplication(req.variable, SmtFactory.createDisjunction(combi));
    }
    else if (req.clause.equals("3a")) handleRpoA(req);
    else if (req.clause.equals("3b")) handleRpoB(req);
    else if (req.clause.equals("3c")) handleRpoC(req);
    else if (req.clause.equals("3d")) handleRpoD(req);
    else if (req.clause.equals("3e")) handleRpoE(req);
    else if (req.clause.equals("3f")) handleRpoF(req);
  }

  private void handleRpoA(HorpoRequirement req) {
    Term l = req.left;
    Type rtype = req.right.queryType();
    ArrayList<Term> args = new ArrayList<Term>();
    for (int i = 1; i <= l.numberArguments(); i++) {
      Term a = l.queryArgument(i);
      if (sameTypeStructure(a.queryType(), rtype)) args.add(a);
    }
    if (args.size() == 0) _problem.require(SmtFactory.createNegation(req.variable));
    else {
      ArrayList<Constraint> vars = new ArrayList<Constraint>();
      for (int i = 0; i < args.size(); i++) {
        vars.add(getVariableFor(req.rule, args.get(i), GEQ, req.right, req.constraint, null));
      }
      _problem.requireImplication(req.variable, SmtFactory.createDisjunction(vars));
    }
  }

  private void handleRpoB(HorpoRequirement req) {
    Term r = req.right;
    if (r.numberArguments() == 0) {
      _problem.require(SmtFactory.createNegation(req.variable));
      return;
    }
    Term a = r.queryImmediateHeadSubterm(r.numberArguments()-1);
    Term b = r.queryArgument(r.numberArguments());
    _problem.requireImplication(req.variable,
      getVariableFor(req.rule, req.left, RPO, a, req.constraint, null));
    _problem.requireImplication(req.variable,
      getVariableFor(req.rule, req.left, RPO, b, req.constraint, null));
  }

  private void handleRpoC(HorpoRequirement req) {
    Term l = req.left;
    Term r = req.right;
    FunctionSymbol f = l.queryRoot();
    if (!r.isFunctionalTerm() || r.queryRoot().equals(f) || r.isValue()) {
      // values are excluded here because this case is already covered by 3f
      _problem.require(SmtFactory.createNegation(req.variable));
    }
    else {
      FunctionSymbol g = r.queryRoot();
      IVar predf = getPrecedenceFor(f);
      IVar predg = getPrecedenceFor(g);
      _problem.requireImplication(req.variable, SmtFactory.createGreater(predf, predg));
      for (int i = 1; i <= r.numberArguments(); i++) {
        _problem.requireImplication(req.variable,
          getVariableFor(req.rule, l, RPO, r.queryArgument(i), req.constraint, null));
      }
    }
  }

  private void handleRpoD(HorpoRequirement req) {
    Term l = req.left, r = req.right;
    FunctionSymbol f = l.queryRoot();
    if (!r.isFunctionalTerm() || !r.queryRoot().equals(f)) {
      _problem.require(SmtFactory.createNegation(req.variable));
      return;
    }
    // to apply lex, status(f) should be Lex, which we represent as 1
    IVar status = getStatusFor(f);
    if (status != null) {   // in the null case, status is automatically lex
      _problem.requireImplication(req.variable, SmtFactory.createEqual(getStatusFor(f),
        SmtFactory.createValue(1)));
    }
    int m = l.numberArguments();
    if (r.numberArguments() < m) m = r.numberArguments();
    // in the case some side has 0 arguments, this case cannot occur
    if (m == 0) _problem.require(SmtFactory.createNegation(req.variable));
    else {
      if (m == 1) {
        BVar x = getVariableFor(req.rule, l.queryArgument(1), GREATER,
                                r.queryArgument(1), req.constraint, null);
        _problem.requireImplication(req.variable, x);
      }
      else {
        IVar index = _problem.createIntegerVariable();
        _problem.require(SmtFactory.createGeq(index, SmtFactory.createValue(1)));
        _problem.require(SmtFactory.createLeq(index, SmtFactory.createValue(m)));
        for (int i = 1; i < m; i++) {
          // create constraint: index > i → l_i ≽ r_i
          BVar ligeqri = getVariableFor(req.rule, l.queryArgument(i), GEQ, r.queryArgument(i),
                                        req.constraint, null);
          Constraint constraint = SmtFactory.createImplication(
            SmtFactory.createGreater(index, SmtFactory.createValue(i)), ligeqri);
          _problem.requireImplication(req.variable, constraint);
        }
        for (int i = 1; i <= m; i++) {
          // create constraint: index = i → l_i ≻ r_i
          BVar ligreri = getVariableFor(req.rule, l.queryArgument(i), GREATER, r.queryArgument(i),
                                        req.constraint, null);
          Constraint constraint = SmtFactory.createImplication(
            SmtFactory.createEqual(index, SmtFactory.createValue(i)), ligreri);
          _problem.requireImplication(req.variable, constraint);
        }
      }
      for (int i = 2; i <= r.numberArguments(); i++) {
        BVar x = getVariableFor(req.rule, l, RPO, r.queryArgument(i), req.constraint, null);
        _problem.requireImplication(req.variable, x);
      }
    }
  }

  /**
   * Given a requirement f l1...ln ▷{φ} f r1...rm by 1e (so a mul step), this adds the constraints
   * that for this requirement to hold, we need status(f) = Mul_k with k ≤ m, and that
   * f l1...ln ▷{φ} for all ri where this is not already automatically implied by the multiset
   * requirements
   */
  private void handleMulBasics(HorpoRequirement req, IVar status) {
    Term r = req.right;
    int m = r.numberArguments();

    // [req] → k > 1 (as k = 1 implies a Lex step)
    _problem.requireImplication(req.variable, SmtFactory.createGreater(status,
        SmtFactory.createValue(1)));
    
    // [req] → k ≤ m (we only require this if f r1 ... rm does not have base type, since otherwise
    // it is already covered by the constraint on the creation of the status variable k)
    if (r.queryType().isArrowType()) {
      _problem.requireImplication(req.variable,
        SmtFactory.createLeq(status, SmtFactory.createValue(m)));
    }

    // [req] → l ▷{φ} r_i for all arguments i; however, we omit 1,2 since the multiset constraints
    // always imply this (for i > 2, it could be that k = 2, and then these are not required)
    for (int i = 3; i <= m; i++) {
      _problem.requireImplication(req.variable,
        getVariableFor(req.rule, req.left, RPO, r.queryArgument(i), req.constraint, null));
    }
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
   * is smaller than status, is true.
   */
  private TreeMap<Integer,BVar> createStrict(BVar reqvar, IVar status, int n) {
    TreeMap<Integer,BVar> ret = new TreeMap<Integer,BVar>();
    ArrayList<Constraint> oneof = new ArrayList<Constraint>();
    for (int j = 1; j <= n; j++) {
      BVar strict_j = _problem.createBooleanVariable();
      ret.put(j, strict_j);
      oneof.add(strict_j);
      if (j > 2) {
        // [req] → ([strict_j] → k ≥ j)
        Constraint constr = SmtFactory.createImplication(strict_j,
          SmtFactory.createGeq(status, SmtFactory.createValue(j)));
        _problem.requireImplication(reqvar, constr);
      }
    }

    // [req] → [strict_1] ∨ ... ∨ [strict_n]
    _problem.requireImplication(reqvar, SmtFactory.createDisjunction(oneof));
    return ret;
  }

  /**
   * Given a requirement f l1...ln ▷{φ} f r1...rm by 1e, this creates variables π(i) ∈ {1..n}
   * for all i ∈ {1,..,m}.  It also adds the requirement that each i ≤ status is mapped to
   * some j ≤ status.
   */
  private TreeMap<Integer,IVar> createProjection(BVar reqvar, IVar status, int n, int m,
                                                 TreeMap<Integer,TreeSet<Integer>> comparable ) {
    // create variables π(i)
    TreeMap<Integer,IVar> pi = new TreeMap<Integer,IVar>();
    for (int i = 1; i <= m; i++) pi.put(i, _problem.createIntegerVariable());
    // require that, for 1 ≤ i ≤ status, 1 ≤ π(i) ≤ status and π(i) ≤ n
    for (int i = 1; i <= m; i++) {
      IVar pi_i = pi.get(i);
      Constraint inotinrange = SmtFactory.createGreater(SmtFactory.createValue(i), status);
      Constraint atleastone = SmtFactory.createGeq(pi_i, SmtFactory.createValue(1));
      Constraint atmostn = SmtFactory.createLeq(pi_i, SmtFactory.createValue(n));
      Constraint atmostk = SmtFactory.createLeq(pi_i, status);
      _problem.requireImplication(reqvar, SmtFactory.createDisjunction(inotinrange, atleastone));
      _problem.requireImplication(reqvar, SmtFactory.createDisjunction(inotinrange, atmostn));
      _problem.requireImplication(reqvar, SmtFactory.createDisjunction(inotinrange, atmostk));
    }
    // require that π(i) != j if l_j and r_i do not have the same type structure
    for (int i = 1; i <= m; i++) {
      TreeSet<Integer> ok = comparable.get(i);
      IVar pi_i = pi.get(i);
      for (int j = 1; j <= n; j++) {
        if (!ok.contains(j)) {
          _problem.requireImplication(reqvar, SmtFactory.createUnequal(pi_i, SmtFactory.createValue(j)));
        }
      }
    }
    return pi;
  }

  private void requirePiEqualityForNonStrict(BVar reqvar, IVar status, int n, int m,
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
          _problem.requireImplication(reqvar, d);
        }
      }
    }
  }

  private void handleRpoE(HorpoRequirement req) {
    Term l = req.left, r = req.right;
    FunctionSymbol f = l.queryRoot();
    if (!r.isFunctionalTerm() || !r.queryRoot().equals(f) || r.numberArguments() <= 1 ||
        l.numberArguments() == 0) {
      _problem.require(SmtFactory.createNegation(req.variable));
      return;
    }
    int n = l.numberArguments(), m = r.numberArguments();
    if (n > m) n = m;
    // we let l = f l1 ... ln (perhaps with more arguments added, but these
    // cannot possibly contribute to the mul relation) and r = f r1 ... rm
    // note that m is at least 2; n may also be 1

    // to apply mul, status(f) should be Mul_k, which we represent as k > 1
    IVar status = getStatusFor(f);
    if (status == null) {   // in the null case, status is automatically lex
      _problem.require(SmtFactory.createNegation(req.variable));
      return;
    }
    handleMulBasics(req, status);
    TreeMap<Integer,TreeSet<Integer>> comparable = createComparable(l, n, r, m);
    TreeMap<Integer,BVar> strict = createStrict(req.variable, status, n);
    TreeMap<Integer,IVar> pi = createProjection(req.variable, status, n, m, comparable);
    requirePiEqualityForNonStrict(req.variable, status, n, m, comparable, strict, pi);

    for (int i = 1; i <= m; i++) {
      Constraint itoobig = SmtFactory.createGreater(SmtFactory.createValue(i), status);
      TreeSet<Integer> ok = comparable.get(i);
      for (int j = 1; j <= n; j++) {
        if (!ok.contains(j)) continue;
        Constraint pinotj = SmtFactory.createUnequal(SmtFactory.createValue(j), pi.get(i));
        Constraint notstrict = SmtFactory.createNegation(strict.get(j));
        // if [req] ∧ i ≤ status ∧ π(i) = j ∧ strict_j then s_i > t_j
        BVar gr = getVariableFor(req.rule, l.queryArgument(j), GREATER, r.queryArgument(i),
                                 req.constraint, null);
        Constraint c = SmtFactory.createDisjunction(
          SmtFactory.createDisjunction(itoobig, pinotj),
          SmtFactory.createDisjunction(notstrict, gr));
        _problem.requireImplication(req.variable, c);
        // if [req] ∧ i ≤ status ∧ π(i) = j ∧ ¬strict_j then s_i ≥ t_j
        BVar geq = getVariableFor(req.rule, l.queryArgument(j), GEQ, r.queryArgument(i),
                                  req.constraint, null);
        c = SmtFactory.createDisjunction(
          SmtFactory.createDisjunction(itoobig, pinotj),
          SmtFactory.createDisjunction(strict.get(j), geq));
        _problem.requireImplication(req.variable, c);
      }
    }
  }

  private void handleRpoF(HorpoRequirement req) {
    Term r = req.right;
    if (r.isValue()) return;    // nothing to require, the variable can be set to true
    if (r.isVariable() && req.constraint.vars().contains(r.queryVariable())) return; // same
    _problem.require(SmtFactory.createNegation(req.variable));
  }

  private HorpoResult solve() {
    Valuation valuation = null;
    switch (Settings.smtSolver.checkSatisfiability(_problem)) {
      case SmtSolver.Answer.YES(Valuation val): valuation = val; break;
      default: return new HorpoResult("Could not find a HORPO proof."); // we are returning MAYBE
    };
    TreeMap<String,Integer> pred = new TreeMap<String,Integer>();
    for (String symbol : _precedence.keySet()) {
      pred.put(symbol, valuation.queryAssignment(_precedence.get(symbol)));
    }
    TreeMap<String,Integer> stat = new TreeMap<String,Integer>();
    for (String symbol : _status.keySet()) {
      stat.put(symbol, valuation.queryAssignment(_status.get(symbol)));
    }
    int bound = _M;
    if (valuation.queryAssignment(_down)) bound = -_M;
    return new HorpoResult(pred, stat, bound);
  }

  /** For use in unit testing */
  String toString(int num1, int num2) {
    StringBuilder ret = new StringBuilder();
    if (num1 == 0) ret.append(_problem.toString());
    else ret.append(_problem.toString(num1));
    int start = 0, end = _todo.size();
    if (num2 > 0 && num2 < end) end = num2;
    if (num2 < 0 && end + num2 > 0) start = end + num2;
    for (int i = start; i < end; i++) {
      ret.append("  " + _todo.get(i).toString() + "\n");
    }
    return ret.toString();
  }

  public String toString() {
    return toString(0, 0);
  }

  /** Only available for the sake of unit testing. */
  int queryIntegerVariableBound() {
    return _M;
  }
}
