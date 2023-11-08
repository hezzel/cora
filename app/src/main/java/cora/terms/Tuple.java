package cora.terms;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import cora.exceptions.IllegalArgumentError;
import cora.exceptions.InappropriatePatternDataError;
import cora.types.Type;
import cora.types.TypeFactory;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A tuple term is a term of the form (t1, ..., tn).
 * In a tuple term, n >= 2 always since they are of product type.
 */
public class Tuple extends TermInherit {
  public ImmutableList<Term> _components;
  public Type _tupleType;

  public void buildTuple(ImmutableList<Term> tms){
    if (tms.size() < 2) throw new IllegalArgumentError(
      "Tuple",
      "constructor",
      "the provided list of terms has " + tms.size() + " elements." +
        "However, tuples can only be created with at least two terms.");

    ImmutableList<Type> tmsTy =
      tms.stream().map(Term::queryType).collect(ImmutableList.toImmutableList());

    _tupleType = TypeFactory.createProduct(tmsTy);
    _components = tms;
  }

  // Constructors ----------------------------------------------------------------------------------

  Tuple(ImmutableList<Term> tms) {
    buildTuple(tms);
  }

  //------------------------------------------------------------------------------------------------

  /**
   * Returns the type of the term.
   */
  @Override
  public Type queryType() {
    return _tupleType;
  }

  /**
   * Returns whether the current term is an unapplied variable.
   */
  @Override
  public boolean isVariable() { return false; }

  /**
   * Returns whether the current term is an unapplied function symbol.
   */
  @Override
  public boolean isConstant() { return false; }

  /**
   * Returns whether the current term has the form f(s1,...,sn) with n ≥ 0.
   */
  @Override
  public boolean isFunctionalTerm() { return false; }

  /**
   * Returns whether the current term has the form x(s1,...,sn) with n ≥ 0.
   */
  @Override
  public boolean isVarTerm() { return false; }

  /**
   * Returns whether the current term has the form h(s1,...,sn) with n > 0.
   */
  @Override
  public boolean isApplication() { return false; }

  /**
   * Returns whether the current term is a lambda-abstraction λx.s.
   */
  @Override
  public boolean isAbstraction() { return false; }

  /**
   * Returns whether the current term is a meta-variable application Z⟨s1,...,sk⟩.
   */
  @Override
  public boolean isMetaApplication() { return false; }

  /**
   * Returns whether the current term has the form (λx.t)(s1,...sn) with n > 0.
   */
  @Override
  public boolean isBetaRedex() { return false; }

  /**
   * Returns whether the current term is a logical term.
   */
  @Override
  public boolean isTheoryTerm() {
    return _components
      .stream()
      .allMatch(Term::isTheoryTerm);
  }

  /**
   * Returns whether the current term is a value (which implies that it is a logical term).
   */
  @Override
  public boolean isValue() { return false; }

  /**
   * Returns the number of arguments; that is, n for a term f(s1,...,sn).
   */
  @Override
  public int numberArguments() { return 0; }

  /**
   * Returns the number of meta-arguments; that is, k for a term Z⟨t1,...,tk⟩(s1,...,sn).
   */
  @Override
  public int numberMetaArguments() { return 0; }

  /**
   * Returns the list of arguments; that is, [s1,...,sn] for a term f(s1,...,sn).
   */
  @Override
  public List<Term> queryArguments() { return null; }

  /**
   * If 1 <= i <= numberArguments, this returns the thus indexed argument.
   * Otherwise, this results in an IndexingError.
   *
   * @param i
   */
  @Override
  public Term queryArgument(int i) {
    return null;
  }

  /**
   * If the current term is a meta-variable application, and its variable has arity k, and
   * 1 ≤ i ≤ k, this returns the thus indexed argument to the meta-variable application.
   * Otherwise, this results in an IndexingError.
   *
   * @param i
   *
   * @throws cora.exceptions.IndexingError
   *
   */
  @Override
  public Term queryMetaArgument(int i) {
    throw new InappropriatePatternDataError(
      "Tuple",
      "queryMetaArgument",
      "trying to query a meta argument from a tuple term."
    );
  }

  /**
   * If the present term is an abstraction λx.s or a beta-redex (λx.s)(t1,...,tn), this returns s.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  @Override
  public Term queryAbstractionSubterm() {
    throw new InappropriatePatternDataError(
      "Tuple",
      "queryAbstractionSubterm",
      "abstraction");
  }

  /**
   * For an applicative term a(s1,...,sn) (where a itself is not an application), the immediate
   * subterms are s1,...,sn.  There are also n+1 head subterms: a, a(s1), a(s1,s2), ...,
   * a(s1,...,sn).  Here, queryImmediateHeadSubterm(i) returns a(s1,...,si).
   * (Note that this should not be used in analysis of first-order term rewriting, since all
   * non-trivial head subterms have a higher type).
   *
   * @param i
   */
  @Override
  public Term queryImmediateHeadSubterm(int i) {
    throw new InappropriatePatternDataError(
      "Tuple",
      "queryImmediateHeadSubterm",
      "this function is only applicable to applicative terms a(s1,...,sn)."
    );
  }

  /**
   * If the term is of application form, so written as h(s1,...,sn) such that h is not an
   * application, this method returns h.
   * In the cases of abstraction or tuple, this method return the term itself.
   * returns h.
   */
  @Override
  public Term queryHead() { return this; }

  /**
   * If this is a functional term f(s1,...,sn) or constant f, this returns the root symbol f.
   *
   * @throws InappropriatePatternDataError if this term is not of the form f(s1,...,sn)
   */
  @Override
  public FunctionSymbol queryRoot() {
    throw new InappropriatePatternDataError(
      "Tuple",
      "queryRoot",
      "a functional term of the form f(s1, ..., sn)."
    );
  }

  /**
   * If the head of this term is a variable x or abstraction λx.s, this returns x.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  @Override
  public Variable queryVariable() {
    throw new InappropriatePatternDataError(
      "Tuple",
      "queryRoot",
      "a functional term of the form f(s1, ..., sn)."
    );
  }

  /**
   * If the head of this term is a meta-application Z⟨s1,...,sk⟩, this returns Z.
   * Otherwise, an InappropriatePatternDataError is thrown.
   */
  @Override
  public MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataError(
      "Tuple",
      "queryRoot",
      "a functional term of the form f(s1, ..., sn)."
    );
  }

  /**
   * If the current term is a value, returns it; if not returns null.
   */
  @Override
  public Value toValue() {
    return null;
  }

  /**
   * Returns true if this term is first-order (so: the subterms at all positions have base type,
   * and no abstractions or variable applications are used), false otherwise.
   */
  @Override
  public boolean isFirstOrder() {
    return false;
  }

  /**
   * Returns true if this term is a pattern (so: non-binder variables are not applied at all, and
   * meta-variables
   */
  @Override
  public boolean isPattern() {
    return false;
  }

  /**
   * Returns true if this term is applicative (so: without binder variables or meta-application)
   */
  @Override
  public boolean isApplicative() {
    return false;
  }

  /**
   * Returns the set of all non-head positions in the current Term, in leftmost innermost order.
   * Note that this set is non-empty as it always contains the empty position (representing the
   * current term).
   * The positions are all Paths, which means they contain the information of the referenced
   * subterm (and the complete path to it).
   */
  @Override
  public List<Path> queryPositions() {
    return null;
  }

  /**
   * Returns the set of all non-head non-root positions in the current term, in leftmost innermost
   * order, except that the associated term of each path is set to the given term rather than the
   * current term; the current term is expected to be the head term of top.
   * This is not meant to be called by classes outside the current package.
   *
   * @param top
   */
  @Override
  public List<Path> queryPositionsForHead(Term top) {
    return null;
  }

  /**
   * Returns the subterm at the given position, assuming that this is indeed a position of the
   * current term.
   * If not, an IndexingError is thrown.
   *
   * @param pos
   */
  @Override
  public Term querySubterm(Position pos) {
    return null;
  }

  /**
   * Returns the term obtained by replacing the subterm at the given position by replacement.
   *
   * @param pos
   * @param replacement
   */
  @Override
  public Term replaceSubterm(Position pos, Term replacement) {
    return null;
  }

  /**
   * Returns the term obtained by replacing the subterm at the given head position by replacement.
   *
   * @param pos
   * @param replacement
   */
  @Override
  public Term replaceSubterm(HeadPosition pos, Term replacement) {
    return null;
  }

  /**
   * This method replaces each variable x in the term by gamma(x) (or leaves x alone if x is not
   * in the domain of gamma), and similarly replaces Z⟨s1,...,sk⟩ with gamma(Z) = λx1...xk.t by
   * t[x1:=s1 gamma,...,xk:=sk gamma]; the result is returned.
   * The original term remains unaltered.  Gamma may be *temporarily* altered to apply the
   * substitution, but is the same at the end of the function as at the start.
   * Note that the result of substituting is a term where all binders in lambdas are freshly
   * generated.
   *
   * @param gamma
   */
  @Override
  public Term substitute(Substitution gamma) {
    return null;
  }

  /**
   * This method either extends gamma so that <this term> gamma = other and returns null, or
   * returns a string describing why other is not an instance of gamma.
   * Whether or not null is returned, gamma is likely to be extended (although without overriding)
   * by this function.
   *
   * @param other
   * @param gamma
   */
  @Override
  public String match(Term other, Substitution gamma) {
    return null;
  }

  /**
   * Adds the string representation of the current term to the given string builder.
   * Some meta-variables and free variables may be renamed by incluing them in "renaming"; if the
   * mapping for a (meta-)variable is not given, then the default name for that variable is used.
   * For names of bound variables, none of the names in the "avoid" set are allowed to be used.
   * The renaming and avoid set may not be null.
   * (This function is primarily intended for the recursive definition of terms; for functions
   * outside the terms package, it is recommended to use the other addToString function instead.)
   *
   * @param builder
   * @param renaming
   * @param avoid
   */
  @Override
  public void addToString(StringBuilder builder, Map<Replaceable, String> renaming, Set<String> avoid) {

  }

  /**
   * Determines the =_α^{μ,ξ,k} relation as described in the documentation.
   *
   * @param term
   * @param mu
   * @param xi
   * @param k
   */
  @Override
  public boolean alphaEquals(Term term, Map<Variable, Integer> mu, Map<Variable, Integer> xi, int k) {
    return false;
  }
}
