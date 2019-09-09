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

package cora.interfaces.terms;

import java.util.ArrayList;
import cora.interfaces.types.Type;

/**
 * Terms are the main object to be rewritten.  There are various kinds of terms,
 * currently including only functional terms f(s1,...,sk) and variables, but in the future it is
 * likely that additional constructions will be allowed.
 *
 * Note; all instances of Term must (and can be expected to) be immutable.
 */

public interface Term {
  public enum TermKind { VARTERM, FUNCTIONALTERM };

  /** Returns the type of the term. */
  Type queryType();

  /** Returns what kind of Term this is. */
  TermKind queryTermKind();

  /** Returns the number of immediate subterms (that is, n for a term f(s1,...,sn)). */
  int numberImmediateSubterms();
  
  /**
   * If 1 <= i <= numberImmediateSubterms, this returns the thus indexed subterm.
   * Otherwise, this results in an IndexingError.
   */
  Term queryImmediateSubterm(int i);

  /**
   * If this is a functional term f(s1,...,sn), this returns the root symbol f.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  FunctionSymbol queryRoot();

  /**
   * If this is a variable x or abstraction λx.s, this returns x.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  Variable queryVariable();

  /**
   * Returns true if this term is first-order (so: the subterms at all standard positions have
   * base type, and no abstractions or variable applications are used), false otherwise.
   */
  boolean queryFirstOrder();

  /**
   * Returns the set of all positions of subterms in the current Term, in leftmost innermost
   * order.
   * Note that this set is non-epmty as it always contains the empty position (representing the
   * current term).
   */
  ArrayList<Position> queryAllPositions();

  /** Returns the set of all variables that occur in the current term. */
  Environment vars();

  /**
   * This adds the variables that occur in the current term into env.
   * Note that this will throw an error if any variable in env has the same name as a variable in
   * the current term (but is a different variable).
   */
  void updateVars(Environment env);

  /**
   * Returns the subterm at the given position, assuming that this is indeed a position of the
   * current term.
   * If not, an IndexingError is thrown.
   */
  Term querySubterm(Position pos);

  /** Returns the term obtained by replacing the subterm at the given position by replacement. */
  Term replaceSubterm(Position pos, Term replacement);

  /**
   * This method replaces each variable x in the term by gamma(x) (or leaves x alone if x is not
   * in the domain of gamma); the result is returned.
   * The original term remains unaltered.  Gamma may be *temporarily* altered to apply the
   * substitution, but is the same at the end of the function as at the start.
   */
  Term substitute(Substitution gamma);

  /**
   * This method either extends gamma so that <this term> gamma = other and returns null, or
   * returns a string describing why other is not an instance of gamma.
   * Whether or not null is returned, gamma is likely to be extended (although without overriding)
   * by this function.
   */
  public String match(Term other, Substitution gamma);

  /**
   * This method returns the substitution gamma such that <this term> gamma = other, if such a
   * substitution exists; if it does not, then null is returned instead.
   */
  public Substitution match(Term other);

  /**Returns a string representation of the term. */
  String toString();

  /**
   * Performs an equality check with the given other term.
   */
  boolean equals(Term term);
}

