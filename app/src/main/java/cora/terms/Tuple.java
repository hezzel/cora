package cora.terms;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import cora.exceptions.*;
import cora.types.Type;
import cora.types.TypeFactory;

/**
 * A tuple term is a term of the form ⦅t1,..., tk⦆, with k ≥ 2.
 */
public class Tuple extends TermInherit {
  private ImmutableList<Term> _components;
  private Type _tupleType;

  /** This private method does correctness checks and sets up the variables. */
  private void buildTuple(List<Term> tms) {
    // check for null arguments
    for (int i = 0; i < tms.size(); i++) {
      if (tms.get(i) == null) {
        throw new NullInitialisationError("Tuple", "passing a null argument to Tuple " +
          "constructor.");
      }
    }

    // configure the set of free variables for this term
    ImmutableList.Builder<Term> builder = ImmutableList.<Term>builder();
    ReplaceableList empty = ReplaceableList.EMPTY;
    ReplaceableList frees = calculateFreeReplaceablesForSubterms(tms, empty);
    ReplaceableList bounds = calculateBoundVariablesAndRefreshSubs(tms, empty, frees, builder);
    _components = builder.build();
    setVariables(frees, bounds);

    // set the type
    ImmutableList<Type> tmsTy =
      tms.stream().map(Term::queryType).collect(ImmutableList.toImmutableList());
    _tupleType = TypeFactory.createProduct(tmsTy);
  }

  // Constructors ----------------------------------------------------------------------------------

  /**
   * Construct a tuple.  This throws an error if some of the given arguments are null, or there are
   * not at least two arguments.
   */
  Tuple(List<Term> tms) {
    if (tms == null) {
      throw new NullInitialisationError("Tuple", "components list");
    }
    if (tms.size() < 2) throw new IllegalArgumentError("Tuple", "constructor",
      "the provided list of terms has " + tms.size() + " elements." +
        "However, tuples can only be created with at least two terms."
    );
    buildTuple(tms);
  }

  /** Short-hand constructor for unit testing. */
  Tuple(Term a, Term b) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(a);
    args.add(b);
    buildTuple(args);
  }

  /** Short-hand constructor for unit testing. */
  Tuple(Term a, Term b, Term c) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(a);
    args.add(b);
    args.add(c);
    buildTuple(args);
  }

  //------------------------------------------------------------------------------------------------

  /**
   * Returns the type of the term.
   */
  @Override
  public Type queryType() { return _tupleType; }


  @Override
  public boolean isTuple() { return true; }

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
   * Returns the number of components in the tuple.
   */
  @Override
  public int numberTupleArguments() {
    return _components.size();
  }

  @Override
  public ImmutableList<Term> queryTupleArguments() { return _components; }

  @Override
  public Term queryTupleArgument(int i) {
    if (i <= 0 || i > _components.size()) {
      throw new IndexingError("Tuple", "queryTupleArgument", i, 1, _components.size());
    }
    return _components.get(i-1);
  }

  /**
   * @throws InappropriatePatternDataError since tuples do not have a primary variable
   */
  @Override
  public Variable queryVariable() {
    throw new InappropriatePatternDataError(
      "Tuple",
      "queryRoot",
      "a varterm, abstraction or beta-redex."
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
   * Returns true if this term is first-order (so: the subterms at all positions have base type,
   * and no abstractions or variable applications are used), false otherwise.
   */
  @Override
  public boolean isFirstOrder() {
    return  _components.stream().allMatch(Term::isFirstOrder);
  }

  /**
   * Returns true if this term is a pattern (so: non-binder variables are not applied at all, and
   * meta-variables
   */
  @Override
  public boolean isPattern() { return _components.stream().allMatch(Term::isPattern); }

  /**
   * Returns true if this term is applicative (so: without binder variables or meta-application)
   */
  @Override
  public boolean isApplicative() {
    return _components.stream().allMatch(Term::isApplicative);
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
    List<Path> pos = new ArrayList<Path>();
    for (int i = 0; i < _components.size(); i++){
      List<Path> compPaths = _components.get(i).queryPositions();
      for (Path compPath : compPaths) {
        pos.add(new TuplePath(this, i + 1, compPath));
      }
    }
    pos.add(new EmptyPath(this));
    return pos;
  }

  /** @return an empty list */
  @Override
  public List<Path> queryPositionsForHead(Term top) { return new ArrayList<Path>(); }

  /**
   * Returns the subterm at the given position, assuming that this is indeed a position of the
   * current term.
   * If not, an IndexingError is thrown.
   *
   * @param pos
   */
  @Override
  public Term querySubterm(Position pos) {
    if (pos.isEmpty()) return this;
    int index = pos.queryComponentPosition();
    if (index < 1 || index > _components.size()) {
      throw new IndexingError("Tuple", "querySubterm", toString(), pos.toString());
    }
    return _components
      .get(index - 1)
      .querySubterm(pos.queryTail());
  }

  /** Returns the term obtained by replacing the subterm at the given position by replacement. */
  @Override
  public Term replaceSubterm(Position pos, Term replacement) {
    return replaceSubterm(new HeadPosition(pos), replacement);
  }

  /**
   * Returns the term obtained by replacing the subterm at the given head position by replacement.
   */
  @Override
  public Term replaceSubterm(HeadPosition pos, Term replacement) {
    if (pos.isEnd()){
      if (pos.queryChopCount() > 0) {
        throw new IndexingError("Tuple", "replaceSubterm", toString(), pos.toString());
      }
      if (!_tupleType.equals(replacement.queryType())) {
        throw new TypingError(
          "Tuple",
          "replaceSubterm",
          "replacement term " + replacement.toString(),
          replacement.queryType().toString(),
          _tupleType.toString()
        );
      }
      return replacement;
    }
    if (!pos.isTuple()) {
      throw new IndexingError("Tuple", "replaceSubterm", toString(), pos.toString());
    }
    int replacementPos = pos.queryComponentPosition();
    if (replacementPos < 1 || replacementPos > _components.size()) {
      throw new IndexingError(
        "Tuple",
        "replaceSubterm",
        this.toString(),
        pos.toString()
      );
    }
    ArrayList<Term> newTupleComponents = new ArrayList<Term>(_components);
    newTupleComponents.set(replacementPos - 1,
      newTupleComponents.get(replacementPos - 1).replaceSubterm(pos.queryTail(), replacement));
    return new Tuple(newTupleComponents);
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
    return new Tuple(_components.stream().map(t -> t.substitute(gamma)).toList());
  }

  /**
   * This method either extends gamma so that <this term> gamma = other and returns null, or
   * returns a string describing why other is not an instance of gamma.
   * Whether null is returned, gamma is likely to be extended (although without overriding)
   * by this function.
   *
   * @param other
   * @param gamma
   */
  @Override
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new
      NullCallError("Application", "match", "argument term (other)");
    if (!other.isTuple()) {
      return other.toString() + " does not instantiate " + toString() + " (not a tuple term).";
    }
    if (_components.size() != other.numberTupleArguments()) {
      return other.toString() + " does not instantiate " + this.toString() + " (mismatch on the " +
        "tuple sizes).";
    }
    for (int i = 0; i < _components.size(); i++) {
      String warning = _components.get(i).match(other.queryTupleArgument(i+1), gamma);
      if (warning != null) return warning;
    }
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
  public void addToString(StringBuilder builder, Map<Replaceable, String> renaming,
                          Set<String> avoid) {
    builder.append("⦅");
    for(int i = 0; i < _components.size(); i++){
      if (i > 0) builder.append(", ");
      _components.get(i).addToString(builder, renaming, avoid);
    }
    builder.append("⦆");
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
    if (!term.isTuple() || !_tupleType.equals(term.queryType())) {
      return false;
    }
    if (_components.size() != term.numberTupleArguments()) return false;
    for (int i = 0; i < _components.size(); i++) {
      if (!_components.get(i).alphaEquals(term.queryTupleArgument(i+1), mu, xi, k)) return false;
    }
    return true;
  }
}
