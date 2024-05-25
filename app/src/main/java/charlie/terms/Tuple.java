/**************************************************************************************************
 Copyright 2023-2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import charlie.exceptions.*;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.position.Position;
import charlie.terms.position.ArgumentPos;

/**
 * A tuple term is a term of the form ⦇t1,..., tk⦈, with k ≥ 2.
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
    if (tms == null) throw new NullInitialisationError("Tuple", "components list");
    if (tms.size() < 2) throw new IllegalArgumentException("Tuple::constructor -- " +
      "the provided list of terms has " + tms.size() + " elements.  " +
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
   * adds all function symbols in the current term to storage
   */
  public void storeFunctionSymbols(Set<FunctionSymbol> storage) {
    for (Term t : _components) t.storeFunctionSymbols(storage);
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
   * @throws InappropriatePatternDataError since tuples do not have a meta-variable
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

  @Override
  public boolean isPattern() { return _components.stream().allMatch(Term::isPattern); }

  @Override
  public boolean isSemiPattern() { return _components.stream().allMatch(Term::isSemiPattern); }

  /**
   * Returns true if all components of this tuple are applicative (so: without binder variables or
   * meta-application)
   */
  @Override
  public boolean isApplicative() {
    return _components.stream().allMatch(Term::isApplicative);
  }

  /**
   * Returns the set of all full subterms of the current Term, along with their positions,
   * in leftmost innermost order.  Note that this set is non-empty as it always contains the
   * current term / empty position as the last element.
   */
  @Override
  public List<Pair<Term,Position>> querySubterms() {
    List<Pair<Term,Position>> ret = new ArrayList<Pair<Term,Position>>();
    for (int i = 0; i < _components.size(); i++){
      List<Pair<Term,Position>> subs = _components.get(i).querySubterms();
      for (Pair<Term,Position> pair : subs) {
        ret.add(new Pair<Term,Position>(pair.fst(), new ArgumentPos(i + 1, pair.snd())));
      }
    }
    ret.add(new Pair<Term,Position>(this, Position.empty));
    return ret;
  }

  /**
   * Returns the subterm at the given (non-empty) position, assuming that this is indeed a position
   * of the current term.  If not, an IndexingError is thrown.
   */
  @Override
  public Term querySubtermMain(Position pos) {
    switch (pos) {
      case ArgumentPos(int index, Position tail):
        if (index <= _components.size()) {
          return _components.get(index-1).querySubterm(tail);
        }
      default:
        throw new IndexingError("Tuple", "querySubterm", toString(), pos.toString());
    }
  }

  /**
   * Returns the term obtained by replacing the subterm at the given (non-empty) position by the
   * given replacement.
   */
  @Override
  public Term replaceSubtermMain(Position pos, Term replacement) {
    switch (pos) {
      case ArgumentPos(int index, Position tail):
        if (index <= _components.size()) {
          ArrayList<Term> newcomps = new ArrayList<Term>(_components);
          newcomps.set(index - 1, newcomps.get(index - 1).replaceSubterm(tail, replacement));
          return new Tuple(newcomps);
        }
      default:
        throw new IndexingError("Tuple", "replaceSubterm", toString(), pos.toString());
    }
  }

  /**
   * Substitutes the tuple by substituting all its components and wrapping the results in a
   * tuple again.
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
   */
  @Override
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullPointerException("Argument term in Application::match");
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

  /** Determines the =_α^{μ,ξ,k} relation as described in the documentation. */
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
