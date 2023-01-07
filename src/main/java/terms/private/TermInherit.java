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

import java.util.List;
import java.util.ArrayList;
import cora.exceptions.IndexingError;

/**
 * A TermInherit supplies default functionality for all instances of Term.
 * This is the functionality that calls other functions in Term to for instance build up a
 * substitution or environment.
 */
abstract class TermInherit implements Term {
  /** Returns the set of all variables occurring in the current term. */
  public Environment vars() {
    Environment env = new Env();
    updateVars(env);
    return env;
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
    Environment env = vars();
    for (Variable x : env) {
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

  /** This method verifies equality to another Term. */
  public boolean equals(Object other) {
    if (other instanceof Term) return equals((Term)other);
    return false;
  }

  /** This method returns a string representation of the current term. */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    addToString(builder);
    return builder.toString();
  }
}

