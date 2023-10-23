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
import java.util.Map;
import java.util.Set;
import cora.types.Type;

/**
 * Terms are the main object to be rewritten, or used to construct rules.  There are various kinds
 * of terms: functional terms f(s1,...,sn), var terms x(s1,...,xn), abstractions λx.s and
 * meta-applications Z⟨s1,...,sk⟩.  (The latter would traditionally be considered a _meta_term
 * rather than a term, but it is convenient to use the same interface for it.)
 *
 * Note: all instances of Term must (and can be expected to) be immutable.
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

  /** Returns whether or not the current term has the form h(s1,...,sn) with n > 0. */
  boolean isApplication();

  /** Returns whether or not the current term is a lambda-abstraction λx.s. */
  boolean isAbstraction();

  /** Returns whether or not the current term is a meta-variable application Z⟨s1,...,sk⟩. */
  boolean isMetaApplication();

  /** Returns whether or not the current term has the form (λx.t)(s1,...sn) with n > 0. */
  boolean isBetaRedex();

  /** Returns whether the sets of variables and meta-variables are empty. */
  boolean isGround();

  /** Returns whether the set of variables contains only non-binder variables. */
  boolean isClosed();

  /** Returns whether the set of meta-variables is emtpy. */
  boolean isTrueTerm();

  /** Returns whether the current term is a logical term. */
  boolean isTheoryTerm();
  
  /** Returns whether the current term is a value (which implies that it is a logical term). */
  boolean isValue();

 /** Returns the number of arguments; that is, n for a term f(s1,...,sn). */
  int numberArguments();

  /** Returns the number of meta-arguments; that is, k for a term Z⟨t1,...,tk⟩(s1,...,sn). */
  int numberMetaArguments();

  /** Returns the list of arguments; that is, [s1,...,sn] for a term f(s1,...,sn). */
  List<Term> queryArguments();
 
  /**
   * If 1 <= i <= numberArguments, this returns the thus indexed argument.
   * Otherwise, this results in an IndexingError.
   */
  Term queryArgument(int i);

  /**
   * If the current term is a meta-variable application, and its variable has arity k, and
   * 1 ≤ i ≤ k, this returns the thus indexed argument to the meta-variable application.
   * Otherwise, this results in an IndexingError.
   */
  Term queryMetaArgument(int i);

  /**
   * If the present term is an abstraction λx.s or a beta-redex (λx.s)(t1,...,tn), this returns s.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  public Term queryAbstractionSubterm();

  /**
   * For an applicative term a(s1,...,sn) (where a itself is not an application), the immediate
   * subterms are s1,...,sn.  There are also n+1 head subterms: a, a(s1), a(s1,s2), ...,
   * a(s1,...,sn).  Here, queryImmediateHeadSubterm(i) returns a(s1,...,si).
   * (Note that this should not be used in analysis of first-order term rewriting, since all
   * non-trivial head subterms have a higher type).
   */
  Term queryImmediateHeadSubterm(int i);

  /** Writing the term as an application h(s1,...,sn) with h not an application, returns h. */
  Term queryHead();

   /**
   * If this is a functional term f(s1,...,sn) or constant f, this returns the root symbol f.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  FunctionSymbol queryRoot();

  /**
   * If the head of this term is a variable x or abstraction λx.s, this returns x.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  Variable queryVariable();

  /**
   * If the head of this term is a meta-application Z⟨s1,...,sk⟩, this returns Z.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  MetaVariable queryMetaVariable();

  /** If the current term is a value, returns it; if not returns null. */
  Value toValue();
  
   /**
   * Returns true if this term is first-order (so: the subterms at all positions have base type,
   * and no abstractions or variable applications are used), false otherwise.
   */
  boolean isFirstOrder();

  /**
   * Returns true if this term is a pattern (so: non-binder variables are not applied at all, and
   * meta-variables 
   */
  boolean isPattern();

  /** Returns true if this term is applicative (so: without binder variables or meta-application) */
  boolean isApplicative();

  /**
   * Returns the set of all non-head positions in the current Term, in leftmost innermost order.
   * Note that this set is non-empty as it always contains the empty position (representing the
   * current term).
   * The positions are all Paths, which means they contain the information of the referenced
   * subterm (and the complete path to it).
   */
  List<Path> queryPositions();

  /**
   * Returns the set of all non-head non-root positions in the current term, in leftmost innermost
   * order, except that the associated term of each path is set to the given term rather than the
   * current term; the current term is expected to be the head term of top.
   * This is not meant to be called by classes outside the current package.
   */
  List<Path> queryPositionsForHead(Term top);

  /**
   * Returns the set of all head-positions in the current Term, in leftmost innermost order.
   * Note that this includes all positions (as these are head positions with 0 chop).
   */
  List<HeadPosition> queryHeadPositions();

  /**
   * Returns the set of all variables occurring freely in the current term.  This may be both binder
   * variables and free variables.
   * Note that two α-equal terms will have the same set of variables.
   */
  Environment<Variable> vars();

  /**
   * Returns the set of all meta-variables that occur in the current term.  Note that, for closed
   * terms, this includes vars(), but it may also include higher meta-variables.
   */
  Environment<MetaVariable> mvars();

  /** 
   * Returns the set of all variables that occur freely in the current term, alongside all
   * meta-variables that occur in it.  All are cast as Replaceables (the parent class for
   * Variable and MetaVariable).
   * This is efficient, as it returns a cached set.
   * This function is primarily meant for package-internal use, but may be used outside the package
   * by some classes.  If you want either variables or meta-variables, use vars() or mvars().
   */
  ReplaceableList freeReplaceables();

  /**
   * Returns the subterm at the given position, assuming that this is indeed a position of the
   * current term.
   * If not, an IndexingError is thrown.
   */
  Term querySubterm(Position pos);

  /**
   * Returns the subterm at the given head position, assuming that this is indeed a head position
   * of the current term.  If not, an IndexingError is thrown.
   */
  Term querySubterm(HeadPosition pos);

  /** Returns the term obtained by replacing the subterm at the given position by replacement. */
  Term replaceSubterm(Position pos, Term replacement);

  /**
   * Returns the term obtained by replacing the subterm at the given head position by replacement.
   */
  Term replaceSubterm(HeadPosition pos, Term replacement);

  /**
   * If the current term has a type σ1 →...→ σn → τ and args = [s1,...,sn] with each si : σi, then
   * this function returns the application of the current term to [s1,...,sn].
   * For example, if the current term is f(3), then the result is f(3,s1,...,sn).
   * If the resulting term cannot be constructed for type reasons, this will throw a TypingError.
   */
  Term apply(List<Term> args);

  /** The same as apply([other]) */
  Term apply(Term other);

  /**
   * This method replaces each variable x in the term by gamma(x) (or leaves x alone if x is not
   * in the domain of gamma), and similarly replaces Z⟨s1,...,sk⟩ with gamma(Z) = λx1...xk.t by
   * t[x1:=s1 gamma,...,xk:=sk gamma]; the result is returned.
   * The original term remains unaltered.  Gamma may be *temporarily* altered to apply the
   * substitution, but is the same at the end of the function as at the start.
   * Note that the result of substituting is a term where all binders in lambdas are freshly
   * generated.
   */
  Term substitute(Substitution gamma);

  /**
   * This method either extends gamma so that <this term> gamma = other and returns null, or
   * returns a string describing why other is not an instance of gamma.
   * Whether or not null is returned, gamma is likely to be extended (although without overriding)
   * by this function.
   */
  String match(Term other, Substitution gamma);

  /**
   * This method returns the substitution gamma such that <this term> gamma = other, if such a
   * substitution exists; if it does not, then null is returned instead.
   */
  Substitution match(Term other);

  /**
   * Provides a string representation of the current term.  Here, variables and meta-variables are
   * renamed as needed to avoid distinct (meta-)variables having the same name.
   */
  String toString();

  /**
   * Adds the string representation of the current term to the given string builder.
   * The caller may rename some meta-variables and free variables by including those in "renaming";
   * if the mapping for a (meta-)variable is not given, then its default name is used (but note
   * that it is not guaranteed that different variables in the same Term have different names).
   * Some free variables may be renamed; if the mapping for a variable is not given, then the
   * default name for that variable is used.
   * To get a suitable renaming, callers can use getUniqueNaming().  You can also supply null,
   * which has the same effect as supplying an empty mapping: no free variables are renamed.)
   */
  void addToString(StringBuilder builder, Map<Replaceable,String> renaming);

  /**
   * This function returns a unique name for every variable and meta-variable occurring in the
   * term.  For use in addToString.
   */
  Map<Replaceable,String> getUniqueNaming();

  /**
   * Performs an equality check with the given other term.
   * Equality is modulo alpha (but this is only relevant for higher-order rewriting with lambdas).
   */
  boolean equals(Term term);

  /* ======== the following functions are intended for internal use in the terms package ======== */

  /**
   * Replaces all the binders in lambdas by fresh variables.
   * (This method is mostly intended for internal use in the terms package, to guarantee that all
   * terms are well-behaved.)
   */
  Term refreshBinders();

  /**
   * Adds the string representation of the current term to the given string builder.
   * Some meta-variables and free variables may be renamed by incluing them in "renaming"; if the
   * mapping for a (meta-)variable is not given, then the default name for that variable is used.
   * For names of bound variables, none of the names in the "avoid" set are allowed to be used.
   * The renaming and avoid set may not be null.
   * (This function is primarily intended for the recursive definition of terms; for functions
    *outside the terms package, it is recommended to use the other addToString function instead.)
   */
  void addToString(StringBuilder builder, Map<Replaceable,String> renaming, Set<String> avoid);

  /**
   * Returns the set of all variables that occur bound in the current term, cast as Replaceables.
   * This is efficient, as it returns a cached set.
   * It is meant for package-intenral use only.  Use vars() or mvars() outside the package.
   */
  ReplaceableList boundVars();

  /** Determines the =_α^{μ,ξ,k} relation as described in the documentation. */
  boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k);
}

