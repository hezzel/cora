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

package cora.termination.reduction_pairs.horpo;

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
 * The HorpoConstraintList keeps track of a number of requirements, each indexed by a unique
 * "defining variable".
 */
class HorpoConstraintList {
  enum HRelation { GREATER, GREATERTHEORY, GREATERMONO, GREATERARGS, GREATERRPO,
                   GEQ, GEQTHEORY, GEQEQUAL, GEQMONO, GEQARGS,
                   GEQNOGR, GEQNOGRTHEORY, GEQNOGREQUAL, GEQNOGRMONO, GEQNOGRARGS,
                   RPO, RPOSELECT, RPOAPPL, RPOCOPY, RPOLEX, RPOMUL, RPOTH };

  /**
   * A HorpoRequirement models an inequality of the form left REL right | constraint, theorvar,
   * where theorval contains variables in left and/or right that may be assumed to be instantiated
   * by ground theory terms.
   * Note that this should include all variables in Var(left) ∪ Var(right) that also occur in
   * Var(constraint).
   */
  record HorpoRequirement(Term left, HRelation relation, Term right, Term constraint,
                          TreeSet<Variable> theoryVariables, BVar variable) { }

  private final TermPrinter _printer;
  private SmtProblem _problem;
  private ArrayList<HorpoRequirement> _constraints;
  private TreeMap<String,BVar> _definingVariables;

  /**
   * Sets up a fresh list, with no requirements yet.
   *
   * The given SmtProblem is used to generate the defining variables: each OrderingRequirement is
   * associated with a unique boolean variable, that may be used to represent its truth in an SMT
   * encoding.
   *
   * The given TermPrinter is used to print the requirements, which is important internally since
   * it is used for requirements caching.  Hence, it is essential that two requiements cannot be
   * printed the same if they are actually different.  Thus, the caller should ensure that all the
   * function symbols that might occur in any requirement passed to the HorpoConstraintList are
   * registered as "avoid" symbols in the given printer.
   */
  HorpoConstraintList(TermPrinter printer, SmtProblem problem) {
    _printer = printer;
    _problem = problem;
    _constraints = new ArrayList<HorpoRequirement>();
    _definingVariables = new TreeMap<String,BVar>();
  }

  /**
   * Stores an inequality l RELATION r | phi, and returns the defining variable.
   *
   * Note: if the inequality is already in the constraint list, then nothing is stored, and the
   * corresponding defining variable is returned.  If the requirement is new, then it is indeed
   * stored and a new defining variable is created.
   */
  BVar store(Term left, HRelation relation, Term right, Term constraint) {
    TreeSet<Variable> constraintvars = new TreeSet<Variable>();
    for (Variable x : constraint.vars()) constraintvars.add(x);
    return store(left, relation, right, constraint, constraintvars);
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
  BVar store(Term left, HRelation relation, Term right, Term constraint, Set<Variable> tvar) {
    // let myvars be the restriction of tvar to those variables that occur in left or right
    TreeSet<Variable> myvars = new TreeSet<Variable>();
    for (Variable x : tvar) {
      if (left.vars().contains(x) || right.vars().contains(x)) myvars.add(x);
    }
    // find the defining variable, or create a new one (in which case the constraint is stored)
    String representation = reqToString(left, relation, right, constraint, myvars);
    BVar ret = _definingVariables.get(representation);
    if (ret != null) return ret;
    ret = _problem.createBooleanVariable(representation);
    _definingVariables.put(representation, ret);
    HorpoRequirement req = new HorpoRequirement(left, relation, right, constraint, myvars, ret);
    _constraints.add(req);
    return ret;
  }

  /** Returns the size of the list (the total number of stored requirements) */
  int size() {
    return _constraints.size();
  }

  /** Returns requirement number i in the list */
  HorpoRequirement get(int i) {
    return _constraints.get(i);
  }

  /** Returns a string representation that uniquely identifies the given constraint */
  private String reqToString(Term left, HRelation relation, Term right, Term constraint,
                             TreeSet<Variable> theorvar) {
    Renaming naming = _printer.generateUniqueNaming(constraint, left, right);
    StringBuilder builder = new StringBuilder();
    _printer.print(left, naming, builder);
    builder.append(switch(relation) {
      case HRelation.GREATER       -> " ≻ ";
      case HRelation.GREATERTHEORY -> " ≻{theory} ";
      case HRelation.GREATERMONO   -> " ≻{mono} ";
      case HRelation.GREATERARGS   -> " ≻{args} ";
      case HRelation.GREATERRPO    -> " ≻{rpo} ";
      case HRelation.GEQ           -> " ≽ ";
      case HRelation.GEQTHEORY     -> " ≽{theory} ";
      case HRelation.GEQEQUAL      -> " ≽{equal} ";
      case HRelation.GEQMONO       -> " ≽{mono} ";
      case HRelation.GEQARGS       -> " ≽{args} ";
      case HRelation.GEQNOGR       -> " ≈ ";
      case HRelation.GEQNOGRTHEORY -> " ≈{theory} ";
      case HRelation.GEQNOGREQUAL  -> " ≈{equal} ";
      case HRelation.GEQNOGRMONO   -> " ≈{mono} ";
      case HRelation.GEQNOGRARGS   -> " ≈{args} ";
      case HRelation.RPO           -> " ▷ ";
      case HRelation.RPOSELECT     -> " ▷{select} ";
      case HRelation.RPOAPPL       -> " ▷{appl} ";
      case HRelation.RPOCOPY       -> " ▷{copy} ";
      case HRelation.RPOLEX        -> " ▷{lex} ";
      case HRelation.RPOMUL        -> " ▷{mul} ";
      case HRelation.RPOTH     -> " ▷{th} ";
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
      builder.append(_constraints.get(i).variable().queryName());
      builder.append("\n");
    }
    return builder.toString();
  }
}

