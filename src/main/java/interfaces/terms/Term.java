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

import java.util.List;
import cora.interfaces.types.Type;

/**
 * Terms are the main object to be rewritten.  There are various kinds of terms, currently
 * including functional terms f(s1,...,sk), var terms x(s1,...,xk) and abstractions λx.s (see also
 * the document on the formalism).
 * In the future it is possible that additional constructions will be allowed, but this will depend
 * on the style of term rewriting system under analysis.
 *
 * Note: all instances of Term must (and can be expected to) be immutable.
 *
 * Note: Term construction must guarantee that a variable cannot occur both free and bound in it;
 * if a violating term is constructed, an IllegalTermError should be thrown.
 */
public interface Term {
  /** Returns the type of the term. */
  Type queryType();

  /** Returns whether or not the current term is an unapplied variable. */
  boolean isVariable();

  /** Returns whether or not the current term is an unapplied function symbol. */
  boolean isConstant();

  /** Returns whether or not the current term has the form f(s1,...,sn) with n ≥ 0. */
  boolean isFunctionalTerm();

  /** Returns whether or not the current term has the form x(s1,...,sn) with n ≥ 0. */
  boolean isVarTerm();

  /** Returns whether or not the current term has the form λx.s. */
  boolean isAbstraction();

  /** Returns the number of immediate subterms (that is, n for a term f(s1,...,sn)). */
  int numberImmediateSubterms();
  
  /**
   * If 1 <= i <= numberImmediateSubterms, this returns the thus indexed subterm.
   * Otherwise, this results in an IndexingError.
   */
  Term queryImmediateSubterm(int i);

  /**
   * For an applicative term a(s1,...,sn) (where a itself is not an application), the immediate
   * subterms are s1,...,sn.  There are also n+1 head subterms: a, a(s1), a(s1,s2), ...,
   * a(s1,...,sn).  Here, queryImmediateHeadSubterm(i) returns a(s1,...,si).
   * An abstraction has no head subterm other than queryImmediateHeadSubterm(0), which is the term
   * itself.
   * (Note that this should not be used in analysis of first-order term rewriting, since all
   * non-trivial head subterms have a higher type).
   */
  Term queryImmediateHeadSubterm(int i);

  /**
   * If this is a functional term f(s1,...,sn) or constant f, this returns the root symbol f.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  FunctionSymbol queryRoot();

  /**
   * If this is a variable x, varterm x(s1,...,sn) or abstraction λx.s, this returns x.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  Variable queryVariable();

  /**
   * Returns true if this term is first-order (so: the subterms at all positions have base type,
   * and no abstractions or variable applications are used), and false otherwise.
   */
  boolean isFirstOrder();

  /**
   * Returns true if this term is a pattern (so: variables are not applied at all, or only to
   * distinct binder-variables).
   */
  boolean isPattern();

  /**
   * Returns the set of all positions of subterms in the current Term, in leftmost innermost
   * order.
   * Note that this set is non-epmty as it always contains the empty position (representing the
   * current term).
   */
  List<Position> queryAllPositions();

  /**
   * Returns the set of all variables that occur freely in the current term.
   * Note that it is allowed for these variables to be marked as "binder vars", as long as they are
   * not bound within the current term.
   */
  Environment freeVars();

  /** Returns the set of all variables that occur bound in the current term. */
  Environment boundVars();

  /**
   * Returns the subterm at the given position, assuming that this is indeed a position of the
   * current term.
   * If not, an IndexingError is thrown.
   */
  Term querySubterm(Position pos);

  /** Returns the term obtained by replacing the subterm at the given position by replacement. */
  Term replaceSubterm(Position pos, Term replacement);

  /**
   * If the current term has a type σ1 →...→ σn → τ and args = [s1,...,sn] with each si : σi, then
   * this function returns the implicit application of the current term to [s1,...,sn].
   * For example, if the current term is f(3), then the result is f(3,s1,...,sn).
   * If the resulting term cannot be constructed for type reasons, this will throw a TypingError.
   */
  Term apply(List<Term> args);

  /** The same as apply([other]) */
  Term apply(Term other);

  /**
   * This method replaces each variable x in the term by gamma(x) (or leaves x alone if x is not
   * in the domain of gamma); the result is returned.
   * The original term remains unaltered.  Gamma may be *temporarily* altered to apply the
   * substitution, but is the same at the end of the function as at the start.
   */
  Term substitute(Substitution gamma);

  /**
   * This method either extends gamma so that <this term> gamma = other and returns null, or
   * returns a string describing why other is not an instance of gamma.  This will only do plain
   * matching: the head variable of a var term will not be instantiated to an abstraction.
   * Whether or not null is returned, gamma is likely to be extended (although without overriding)
   * by this function.
   */
  public String match(Term other, Substitution gamma);

  /**
   * This method returns the substitution gamma such that <this term> gamma = other, if such a
   * substitution exists; if it does not, then null is returned instead.  This will only do plain
   * matching: the head variable of a var term will not be instantiated to an abstraction.
   */
  public Substitution match(Term other);

  /** Returns a string representation of the term. */
  String toString();

  /**
   * This function returns a string representation of the term, where variables are renamed using
   * the given renamer.
   */
  String toString(VariableNamer renamer);

  /**
   * Returns a string representation of the term, where variables are renamed in such a way that
   * each variable has a unique name.
   */
  String toPrettyString();

  /**
   * Performs an equality check with the given other term.
   */
  boolean equals(Term term);
}

