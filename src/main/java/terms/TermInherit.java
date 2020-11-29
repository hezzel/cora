/**************************************************************************************************
 Copyright 2019 Cynthia Kop

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
import java.util.Map;
import java.util.TreeMap;
import cora.exceptions.IndexingError;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.Environment;
import cora.interfaces.terms.Alphabet;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.VariableNamer;
import cora.terms.positions.*;

/**
 * A TermInherit supplies default functionality for all instances of Term.
 * This is the functionality that calls other functions in Term to for instance build up a
 * substitution or environment.
 */
abstract class TermInherit implements Term {
  private EnvironmentPair _varsCache = null;

  abstract EnvironmentPair allVars();

  /**
   * Should be called at the end of each constructor, to set up the cache of the free and bound
   * variables.
   * This is essential to fail quickly when a term has inconsistent variables (so the same variable
   * occurring both free and bound).
   */
  protected void initiateVars() {
    _varsCache = allVars();
  }

  /** Returns the set of all variables occurring freely in the current term. */
  public Environment freeVars() {
    return _varsCache.freeVars();
  }

  /** Returns the set of all variables occurring bound in the current term. */
  public Environment boundVars() {
    return _varsCache.boundVars();
  }

  /** Returns all the positions in the present term. */
  public List<Position> queryAllPositions() {
    List<Position> ret = new ArrayList<Position>();
    for (int i = 1; i <= numberImmediateSubterms(); i++) {
      List<Position> subposses = queryImmediateSubterm(i).queryAllPositions();
      for (int j = 0; j < subposses.size(); j++) {
        ret.add(new SubPosition(i, subposses.get(j), this));
      }   
    }
    ret.add(new RootPosition());
    return ret;
  }

  /** Returns the given subterm in the term. */
  public Term querySubterm(Position pos) {
    if (pos.isEmpty()) return this;

    int i = pos.queryArgumentPosition();
    if (i <= 0 || i > numberImmediateSubterms()) {
      throw new IndexingError(this.getClass().getSimpleName(), "querySubterm", toString(),
                              pos.toString());
    }
    if ((pos.isFunctionalPosition() && !isFunctionalTerm()) ||
        (pos.isVartermPosition() && !isVarTerm()) ||
        (pos.isAbstractionPosition() && !isAbstraction())) {
      throw new IndexingError(this.getClass().getSimpleName(), "querySubterm", toString(),
                              pos.toString() + "[position kind mismatch]");
    }
    return queryImmediateSubterm(i).querySubterm(pos.queryTail());
  }

  /** Applies the current term (with functional type) to other. */
  public Term apply(Term other) {
    List<Term> args = new ArrayList<Term>();
    args.add(other);
    return apply(args);
  }

  /** Same as match(other, subst), but it creates a fresh substitution and returns the result. */
  public Substitution match(Term other) {
    Substitution gamma = new Subst();
    if (match(other, gamma) == null) return gamma;
    return null;
  }

  /** This method forwards equality to alpha-equality. */
  public boolean equals(Term other) {
    return alphaEquals(other, new TreeMap<Variable,Integer>(), new TreeMap<Variable,Integer>(), 1);
  }

  /** This method verifies equality to another Term. */
  public boolean equals(Object other) {
    if (other instanceof Term) return equals((Term)other);
    return false;
  }

  /** @return a string representation of the current term */
  public String toString() {
    return toString(new DefaultVariableNamer());
  }

  /**
   * This method returns a string representation of the current term, where variables are renamed
   * so that each variable has a unique name.
   * Variable names are chosen to be disjoint from the alphabet; if this is not desired, then
   * sigma = null should be chosen.
   */
  public String toPrettyString(Alphabet sigma) {
    return toString(new CleverVariableNamer(sigma, freeVars()));
  }
}

