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
 * All inheriting classes should make sure to call setVariables in their constructor, to set up the
 * set of variables occurring in the term.
 */
abstract class TermInherit implements Term {
  private VariableList _freeVariables;
  private VariableList _boundVariables;

  /**
   * Sets the set of all free variables occurring in this term to vs, and the set of bound
   * variables to empty.
   * One of the setVariables functions should be called from the constructor, and only there.
   */
  protected void setVariables(VariableList vs) {
    if (_freeVariables != null) throw new Error("Setting VariableList twice for " +
      this.getClass().getSimpleName());
    _freeVariables = vs;
    _boundVariables = VarList.EMPTY;
  }

  /**
   * Sets the sets of all free and all bound variables occuring in this term.
   * One of the setVariables functions should be called from the constructor, and only there.
   */
  protected void setVariables(VariableList frees, VariableList bounds) {
    if (_freeVariables != null) throw new Error("Setting VariableList twice for " +
      this.getClass().getSimpleName());
    _freeVariables = frees;
    if (bounds == null) _boundVariables = VarList.EMPTY;
    else _boundVariables = bounds;
  }

  /** Returns a combined variable list for the given subterms, which also includes extra. */
  protected static VariableList calculateFreeVariablesForSubterms(List<Term> subs,
                                                                  VariableList extra) {
    VariableList largest = extra;
    int best = 0;
    for (int i = 0; i < subs.size(); i++) {
      if (subs.get(i).vars().size() > largest.size()) {
        best = i + 1;
        largest = subs.get(i).vars();
      }
    }
    // combine the rest into it!
    VariableList frees = largest;
    if (best != 0) frees = frees.combine(extra);
    for (int i = 0; i < subs.size(); i++) {
      if (best != i + 1) frees = frees.combine(subs.get(i).vars());
    }
    return frees;
  }

  /**
   * Refreshes bound variables in the given list if necessary to ensure that they do not overlap
   * with the variables in the given "avoid" set (to ensure well-behavedness of terms), and
   * returns the resulting combined set of bound variables, including all those in "include".
   */
  protected static VariableList calculateBoundVariablesAndRefreshSubterms(List<Term> subs,
                                                                          VariableList include,
                                                                          VariableList avoid) {
    for (int i = 0; i < subs.size(); i++) {
      VariableList vs = subs.get(i).boundVars();
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
  public VariableList vars() {
    if (_freeVariables == null) throw new Error("Variable list has not been set up for " +
      this.getClass().getSimpleName());
    return _freeVariables;
  }

  /** Returns the set of all variables occurring bound in the current term. */
  public VariableList boundVars() {
    if (_freeVariables == null) throw new Error("Variable list has not been set up for " +
      this.getClass().getSimpleName());
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

  /** Returns true if the set vars() is empty. */
  public boolean isGround() {
    return vars().size() == 0;
  }

  /** Returns true if vars() contains only non-binder variables. */
  public boolean isClosed() {
    VariableList vs = vars();
    for (Variable x : vs) {
      if (x.isBinderVariable()) return false;
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

  /** Returns te present term with all binder-variables replaced by fresh ones. */
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
    addToString(builder, _freeVariables.getUniqueNaming());
    return builder.toString();
  }

  /** This function adds a representation of the current term to the given builder. */
  public void addToString(StringBuilder builder, Map<Variable,String> renaming) {
    TreeSet<String> avoid = new TreeSet<String>();
    if (renaming == null) renaming = new TreeMap<Variable,String>();
    for (Variable x : _freeVariables) {
      String name = x.queryName();
      avoid.add(name);
      if (renaming.containsKey(x)) avoid.add(renaming.get(x));
    }
    addToString(builder, renaming, avoid);
  }
}

