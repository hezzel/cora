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

import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import charlie.terms.*;
import charlie.smt.*;

/**
 * The HorpoConstraintList is the core ingredient of the Horpo reduction pair.
 *
 * The HorpoConstraintList keeps track of a number of requirements, each indexed by a unique
 * "defining variable".  The HorpoConstraintList also keeps track of the HorpoParameters, including
 * an SmtProblem.
 *
 * To simplify the HorpoConstraintList, a requirement in the list (that hasn't yet been handled) is
 * expressed as an SMT formula over its defining variable, and the defining variables of simpler SMT
 * problems (e.g., for a requirement "f(x,y) ▷ r | φ by select" we store the constraint
 * [x ▷ r | φ by select] → [x ≽ r | φ] ∨ [y ≽ r | φ]).  The simpler SMT problems are also added to
 * the HorpoConstraintList and simplified in their turn, until the original list of ordering
 * requirements is reduced to an SMT problem that expresses: FORALL initial inequality: IF
 * <defining variable of that inequality> THEN that inequality holds.
 */
class HorpoConstraintList {
  public static final String GREATER = "≻";
  public static final String GEQ = "≽";
  public static final String GEQNOGR = "≈";
  public static final String RPO = "▷";

  /**
   * A HorpoRequirement models a constraint inequality of the form
   *    left REL right | constraint, theorvar by clause
   * where theorval contains variables in left and/or right that may be assumed to be instantiated
   * by ground theory terms
   * Note that this should include all variables in Var(left) ∪ Var(right) that also occur in
   * Var(constraint).
   * Clause is also allowed to be null to represnet the inequality:
   *    left REL right | constraint, theorvar
   */
  private record HorpoRequirement(Term left, String relation, Term right, Term constraint,
                                  TreeSet<Variable> theoryVariables, String clause, BVar variable) {
  }

  private final HorpoParameters _parameters;
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

    _constraints = new ArrayList<HorpoRequirement>();
    _handled = 0;
    _definingVariables = new TreeMap<String,BVar>();
  }

  /**
   * Stores a requirement for the given inequality, and returns the defining variable.  The
   * relation should be one of the constants (e.g., GREATER, GEQ) defined in the class.
   *
   * Note: if the requirement is already in the constraint list, then nothing is stored, and the
   * corresponding defining variable is returned.  If the requirement is new, then it is indeed
   * stored and a new defining variable is created.
   */
  public BVar store(Term left, String relation, Term right, Term constraint) {
    TreeSet<Variable> constraintvars = new TreeSet<Variable>();
    for (Variable x : constraint.vars()) constraintvars.add(x);
    return getVariableFor(left, relation, right, constraint, constraintvars, null);
  }

  /**
   * Stores a requirement for the given inequality, and returns the defining variable.  The given
   * set of theory variables (variables that can be assumed to be instantiated only with ground
   * theory terms) should include all the variables in the constraint.  The relation should be one
   * of the constants (e.g., GREATER, GEQ) defined in the class.
   *
   * Note: if the requirement is already in the constraint list, then nothing is stored, and the
   * corresponding defining variable is returned.  If the requirement is new, then it is indeed
   * stored and a new defining variable is created.
   */
  public BVar store(Term left, String relation, Term right, Term constraint, Set<Variable> tvar) {
    return getVariableFor(left, relation, right, constraint, new TreeSet<Variable>(tvar), null);
  }

  /**
   * Internal function handling the functionality of store, and which can also be used to store
   * relations that come with a clause (e.g., left RPO right BY select).
   *
   * The given TreeSet is the property of HorpoConstraintList, but could be used as part of
   * another requirement so should not be modified.  The given clause is allowed to b enull.
   *
   * This is left default rather than private for the sake of unit testing.
   */
  BVar getVariableFor(Term left, String relation, Term right, Term constraint,
                      TreeSet<Variable> tvar, String clause) {
    // ensure that tvar only contains variables that occur in left or right
    TreeSet<Variable> myvars = new TreeSet<Variable>();
    for (Variable x : tvar) {
      if (left.vars().contains(x) || right.vars().contains(x)) myvars.add(x);
    }
    if (myvars.size() != tvar.size()) tvar = myvars;
    // find the defining variable, or create a new one (in which case the constraint is stored
    String representation = reqToString(left, relation, right, constraint, tvar, clause);
    BVar ret = _definingVariables.get(representation);
    if (ret != null) return ret;
    ret = _parameters.queryProblem().createBooleanVariable(representation);
    _definingVariables.put(representation, ret);
    HorpoRequirement req =
      new HorpoRequirement(left, relation, right, constraint, tvar, clause, ret);
    _constraints.add(req);
    return ret;
  }

  /** Returns a string representation that uniquely identifies the given constraint */
  private String reqToString(Term left, String relation, Term right, Term constraint,
                             TreeSet<Variable> theorvar, String clause) {
    TermPrinter.Renaming naming = _printer.generateUniqueNaming(constraint, left, right);
    StringBuilder builder = new StringBuilder();
    _printer.print(left, naming, builder);
    builder.append(" ");
    builder.append(relation);
    builder.append(" ");
    _printer.print(right, naming, builder);
    builder.append(" | ");
    _printer.print(constraint, naming, builder);
    builder.append(" {");
    for (Variable v : theorvar) {
      builder.append(" ");
      _printer.print(v, naming, builder);
    }
    builder.append(" }");
    if (clause != null) builder.append(" by " + clause);
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

  /** This does a single simplification step, sipmlifying one HorpoRequirement in the list. */
  public void simplify() {
    if (_handled >= _constraints.size()) return;
    HorpoRequirement req = _constraints.get(_handled);
    _handled++;
    if (req.relation.equals(GREATER)) handleGreater(req);
    else if (req.relation.equals(GEQ)) handleGeq(req);
    else if (req.relation.equals(GEQNOGR)) handleGeqNoGr(req);
    else handleRpo(req);
  }

  /***********************************************************************************************/
  /* The functions below all serve to simplify different kinds of HorpoConstraints.              */
  /***********************************************************************************************/

  /** This simplifies requirements of the form: left ≻ right | constraint BY clause */
  public void handleGreater(HorpoRequirement req) {
  }

  /** This simplifies requirements of the form: left ≽ right | constraint BY clause */
  public void handleGeq(HorpoRequirement req) {
  }

  /** This simplifies requirements of the form: left ≈ right | constraint BY clause */
  public void handleGeqNoGr(HorpoRequirement req) {
  }

  /** This simplifies requirements of the form: left ▷ right | constraint BY clause */
  public void handleRpo(HorpoRequirement req) {
  }
}

