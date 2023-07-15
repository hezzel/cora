/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import cora.exceptions.IndexingError;

/**
 * A TermInherit supplies default functionality for all instances of Term.
 * This is the functionality that calls other functions in Term to for instance build up a
 * substitution or environment.
 * All inheriting classes should make sure to call setVariables in their constructor, to set up
 * the set of variables and meta-variables occurring in the term.
 */
abstract class TermInherit implements Term {
  private ReplaceableList _freeReplaceables;
  private ReplaceableList _boundVariables;

  /**
   * Sets the set of all meta-variables and free variables occurring in this term to vs, and the
   * set of bound variables to empty.
   * One of the setVariables functions should be called from the constructor, and only there.
   */
  protected void setVariables(ReplaceableList vs) {
    if (_freeReplaceables != null) throw new Error("Setting ReplaceableList twice for " +
      this.getClass().getSimpleName());
    _freeReplaceables = vs;
    _boundVariables = ReplaceableList.EMPTY;
  }

  /**
   * Sets the sets of all free/meta and all bound variables occuring in this term.
   * One of the setVariables functions should be called from the constructor, and only there.
   */
  protected void setVariables(ReplaceableList frees, ReplaceableList bounds) {
    if (_freeReplaceables != null) throw new Error("Setting ReplaceableList twice for " +
      this.getClass().getSimpleName());
    _freeReplaceables = frees;
    if (bounds == null) _boundVariables = ReplaceableList.EMPTY;
    else _boundVariables = bounds;
  }

  /** Returns a combined replaceable list for the given subterms, which also includes extra. */
  protected static ReplaceableList calculateFreeReplaceablesForSubterms(List<Term> subs,
                                                                        ReplaceableList extra) {
    ReplaceableList largest = extra;
    int best = 0;
    for (int i = 0; i < subs.size(); i++) {
      if (subs.get(i).freeReplaceables().size() > largest.size()) {
        best = i + 1;
        largest = subs.get(i).freeReplaceables();
      }
    }
    // combine the rest into it!
    ReplaceableList frees = largest;
    if (best != 0) frees = frees.combine(extra);
    for (int i = 0; i < subs.size(); i++) {
      if (best != i + 1) frees = frees.combine(subs.get(i).freeReplaceables());
    }
    return frees;
  }

  /**
   * Refreshes bound variables in the given list if necessary to ensure that they do not overlap
   * with the variables in the given "avoid" set (to ensure well-behavedness of terms), and
   * returns the resulting combined set of bound variables, including all those in "include".
   */
  protected static ReplaceableList calculateBoundVariablesAndRefreshSubs(List<Term> subs,
                                                                         ReplaceableList include,
                                                                         ReplaceableList avoid) {
    for (int i = 0; i < subs.size(); i++) {
      ReplaceableList vs = subs.get(i).boundVars();
      if (vs.size() > 0) {
        if (!vs.getOverlap(avoid).isEmpty()) {
          subs.set(i, subs.get(i).refreshBinders());
          vs = subs.get(i).boundVars();
        }
        if (include.size() == 0) include = vs;
        else include = include.combine(vs);
      }   
    }
    return include;
  }

  /** Returns the set of all variables occurring free in the current term. */
  public Environment<Variable> vars() {
    if (_freeReplaceables == null) throw new Error("Variable list requested when it has not been " +
      "set up for " + this.getClass().getSimpleName());
    return new VariableEnvironment(_freeReplaceables);
  }

  /** Returns the set of all meta-variables occurring in the current term. */
  public Environment<MetaVariable> mvars() {
    if (_freeReplaceables == null) throw new Error("Meta-variable list requested when it has not " +
      "been set up for " + this.getClass().getSimpleName());
    return new MetaVariableEnvironment(_freeReplaceables);
  }

  /** Returns the set of all meta-variables and variables occurring free in the current term. */
  public ReplaceableList freeReplaceables() {
    if (_freeReplaceables == null) throw new Error("Replaceable list has not been set up for " +
      this.getClass().getSimpleName() + " when requesting free replaceables.");
    return _freeReplaceables;
  }

  /** Returns the set of all variables occurring bound in the current term. */
  public ReplaceableList boundVars() {
    if (_freeReplaceables == null) throw new Error("Replaceable list has not been set up for " +
      this.getClass().getSimpleName() + " when requesting bound variables");
    return _boundVariables;
  }

  /** Applies the current term (with functional type) to other. */
  public Term apply(Term other) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(other);
    return apply(args);
  }

  /** Same as match(other, subst), but it creates a fresh substitution and returns the result. */
  public Substitution match(Term other) {
    Substitution gamma = new Subst();
    if (match(other, gamma) == null) return gamma;
    return null;
  }

  /** Returns true if there are no free variables (meta-variables are allowed). */
  public boolean isGround() {
    return _freeReplaceables.size() == 0;
  }

  /** Returns true if freeReplaceables() contains no binder variables. */
  public boolean isClosed() {
    ReplaceableList vs = freeReplaceables();
    for (Replaceable x : vs) {
      if (x.queryReplaceableKind() == Replaceable.KIND_BINDER) return false;
    }
    return true;
  }

  /** Returns true if freeReplaceables() contains no meta-variables. */
  public boolean isTrueTerm() {
    ReplaceableList vs = freeReplaceables();
    for (Replaceable x : vs) {
      if (x.queryReplaceableKind() == Replaceable.KIND_METAVAR) return false;
    }
    return true;
  }

  /** Returns the set of all head positions for this term, in leftmost innermost order. */
  public ArrayList<HeadPosition> queryHeadPositions() {
    List<Path> posses = queryPositions();
    ArrayList<HeadPosition> ret = new ArrayList<HeadPosition>();
    for (int i = 0; i < posses.size(); i++) {
      Term t = posses.get(i).queryCorrespondingSubterm();
      for (int j = t.numberArguments(); j > 0; j--) {
        ret.add(new HeadPosition(posses.get(i), j));
      }
      ret.add(new HeadPosition(posses.get(i)));
    }
    return ret;
  }

  /** Returns the subterm at the given head position. */
  public Term querySubterm(HeadPosition hpos) {
    Term sub = querySubterm(hpos.queryPosition());
    int chop = hpos.queryChopCount();
    if (chop == 0) return sub;
    List<Term> args = sub.queryArguments();
    Term head = sub.queryHead();
    if (args.size() < chop) {
      throw new IndexingError("TermInherit", "querySubTerm(HeadPosition)", chop,
        0, args.size());
    }
    return head.apply(args.subList(0, args.size()-chop));
  }

  /** Returns the present term with all binder-variables replaced by fresh ones. */
  public Term refreshBinders() {
    return substitute(new Subst());
  }

  /** 
   * If the current term is h(t1,...,tk) and has a type σ1 →...→ σn → τ and args = [s1,...,sn] with
   * each si : σi, then this function returns h(t1,...,tk,s1,...,sn).
   */
  public Term apply(List<Term> args) {
    if (args.size() == 0) return this;
    return new Application(this, args);
  }

  /** This method verifies equality to another Term. */
  public boolean equals(Term other) {
    if (other == null) return false;
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    return alphaEquals(other, mu, xi, 1);
  }

  /** This method verifies equality to another Java object. */
  public boolean equals(Object other) {
    if (other instanceof Term) return equals((Term)other);
    return false;
  }

  /** This method returns a string representation of the current term. */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    addToString(builder, _freeReplaceables.getUniqueNaming());
    return builder.toString();
  }

  /** This function adds a representation of the current term to the given builder. */
  public void addToString(StringBuilder builder, Map<Replaceable,String> renaming) {
    TreeSet<String> avoid = new TreeSet<String>();
    if (renaming == null) renaming = new TreeMap<Replaceable,String>();
    for (Replaceable x : _freeReplaceables) {
      String name = x.queryName();
      avoid.add(name);
      if (renaming.containsKey(x)) avoid.add(renaming.get(x));
    }
    addToString(builder, renaming, avoid);
  }

  /** This function returns the default unique naming scheme for this term. */
  public TreeMap<Replaceable,String> getUniqueNaming() {
    return _freeReplaceables.getUniqueNaming();
  }
}

