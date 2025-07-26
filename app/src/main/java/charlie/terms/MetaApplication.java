/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

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
import java.util.TreeSet;
import charlie.exceptions.*;
import charlie.util.Pair;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.terms.position.Position;
import charlie.terms.position.MetaPos;

/**
 * A MetaApplication is a term of the form Z⟨s1,...,sk⟩ where Z is a meta-variable with arity
 * k ≥ 1.  MetaApplications of the form Z⟨⟩ are viewed as non-binder variables, so should be
 * created as a Var instead.
 */
class MetaApplication extends TermInherit {
  public MetaVariable _metavar;
  public ImmutableList<Term> _args;

  /**
   * This constructor is used to create a term mvar⟨s1,...,sk⟩ with k ≥ 1.
   * Throws an error if k does not match the arity of the meta-variable, if args is empty or if the
   * types of the arguments are not the expected input types of the meta-variable.
   */
  MetaApplication(MetaVariable mvar, List<Term> args) {
    if (mvar == null) throw new NullStorageException("MetaApplication", "meta-variable");
    if (args == null) throw new NullStorageException("MetaApplication", "argument list");
    _metavar = mvar;
    
    if (args.size() == 0) {
      throw new IllegalArgumentException("It is not legal to create a MetaApplication with no " +
        "arguments: this should be done through the Var class, since a meta-application " +
        "without arguments is just a non-binder variable.");
    }
    if (args.size() != mvar.queryArity()) {
      throw new TypingException("Arity error constructing meta-variable application: " +
        "meta-variable ", mvar, " has arity " + mvar.queryArity() + " but is given " +
        args.size() + " arguments.");
    }

    for (int i = 0; i < args.size(); i++) {
      Term arg = args.get(i);
      if (arg == null) {
        throw new NullStorageException("MetaApplication", "passing a null argument to " +
          "meta-variable application for " + mvar.queryName() + ".");
      }
      if (!arg.queryType().equals(mvar.queryInputType(i+1))) {
        throw new TypingException("Typing error constructing meta-variable application: " +
          "imput type " + (i+1) + " of meta-variable ", mvar, " is ", mvar.queryInputType(i+1) +
          ", while the argument term ", arg, " has type ", arg.queryType());
      }
    }
    ImmutableList.Builder<Term> builder = ImmutableList.<Term>builder();
    ReplaceableList empty = ReplaceableList.EMPTY;
    ReplaceableList start = new ReplaceableList(_metavar);
    ReplaceableList frees = calculateFreeReplaceablesForSubterms(args, start);
    ReplaceableList bounds = calculateBoundVariablesAndRefreshSubs(args, empty, frees, builder);
    _args = builder.build();
    setVariables(frees, bounds);
  }

  /** @return the output type of the meta-variable. */
  public Type queryType() {
    return _metavar.queryOutputType();
  }

  public boolean isMetaApplication() {
    return true;
  }

  public boolean isApplicative() {
    return false;
  }

  public boolean isFirstOrder() {
    return false;
  }

  public boolean isVarTerm() {
    return false;
  }

  public boolean isTheoryTerm() {
    return false;
  }

  /** Adds all function symbols in the present term to storage. */
  public void storeFunctionSymbols(Set<FunctionSymbol> storage) {
    for (Term t : _args) t.storeFunctionSymbols(storage);
  }

  /** @return the number of meta-arguments */
  public int numberMetaArguments() {
    return _args.size();
  }

  /** @return the list of meta-arguments */
  public ImmutableList<Term> queryMetaArguments() {
    return _args;
  }

  /** If this term is Z⟨s1,...,sk⟩, returns si. */
  public Term queryMetaArgument(int i) {
    if (i <= 0 || i > _args.size()) {
      throw new IndexOutOfBoundsException("MetaApplication::queryMetaArgument(" + i + ") called " +
        "on meta-variable application with " + _args.size() + " arguments.");
    }
    return _args.get(i-1);
  }

  /** @throws InappropriatePatternDataException */
  public Variable queryVariable() {
    throw new InappropriatePatternDataException("MetaApplication", "queryVariable",
      "var terms or abstractions");
  }

  /** @return the metavariable for this meta-application */
  public MetaVariable queryMetaVariable() {
    return _metavar;
  }

  /** Returns true if this meta-application is applied to distinct binder variables. */
  public boolean isPattern() {
    if (freeReplaceables().size() != _args.size() + 1) return false;
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).isVariable()) return false;
      if (!_args.get(i).queryVariable().isBinderVariable()) return false;
    }
    return true;
  }

  /** Returns true if this meta-application is applied to distinct binder variables. */
  public boolean isSemiPattern() {
    return isPattern();
  }

  /**
   * Returns all full subterms and their respective positions, from from left to right, with the
   * current term and empty position in the end.
   */
  public List<Pair<Term,Position>> querySubterms() {
    List<Pair<Term,Position>> ret = new ArrayList<Pair<Term,Position>>();
    for (int i = 0; i < _args.size(); i++) {
      List<Pair<Term,Position>> subs = _args.get(i).querySubterms();
      for (int j = 0; j < subs.size(); j++) {
        ret.add(new Pair<Term,Position>(subs.get(j).fst(), new MetaPos(i+1, subs.get(j).snd())));
      }
    }
    ret.add(new Pair<Term,Position>(this, Position.empty));
    return ret;
  }

  /** @return the subterm at the given (non-empty) position */
  public Term querySubtermMain(Position pos) {
    switch (pos) {
      case MetaPos(int index, Position tail):
        if (index <= _args.size()) return _args.get(index-1).querySubterm(tail);
      default:
        throw new InvalidPositionException(this, pos, "querying subterm of meta-application");
    }
  }

  /**
   * @return a copy of the term with the subterm at the given (non-empty) position replaced by
   * replacement, if such a position exists; otherwise throws an InvalidPositionException.
   */
  public Term replaceSubtermMain(Position pos, Term replacement) {
    switch (pos) {
      case MetaPos(int index, Position tail):
        if (index <= _args.size()) {
          ArrayList<Term> newargs = new ArrayList<Term>(_args);
          newargs.set(index-1, _args.get(index-1).replaceSubterm(tail, replacement));
          return new MetaApplication(_metavar, newargs);
        }
      default:
        throw new InvalidPositionException(this, pos, "replacing subterm of meta-application");
    }
  }

  /**
   * This method replaces each variable x in the term by gamma(x) (or leaves x alone if x is not
   * in the domain of gamma), and each meta-application Z[s1,...,sk] with γ(Z) = λx1...xk.t by
   * t[x1:=s1γ,...,xk:=skγ]; the result is returned.
   */
  public Term substitute(Substitution gamma) {
    if (gamma == null) throw new NullPointerException("Substitution in Application::substitute");
    ArrayList<Term> newArgs = new ArrayList<Term>();
    for (int i = 0; i < _args.size(); i++) newArgs.add(_args.get(i).substitute(gamma));
    Term value = gamma.get(_metavar);
    if (value == null) return new MetaApplication(_metavar, newArgs);
    Substitution delta = new Subst();
    Term v = value;
    for (int i = 0; i < newArgs.size(); i++) {
      if (!v.isAbstraction()) {
        throw new TypingException("Arity error when trying to substitute ", _metavar, " by ",
          value, ": meta-variable takes " + newArgs.size() + " arguments, so there should be " +
          "at least this many abstractions!");
      }
      Variable x = v.queryVariable();
      v = v.queryAbstractionSubterm();
      delta.replace(x, newArgs.get(i));
    }
    return v.substitute(delta);
  }

  /**
   * This method either extends gamma so that <this term> gamma = other and returns null, or
   * returns a string describing why other is not an instance of gamma.
   * This function may only be called if the meta-application is a semi-pattern; that is, the
   * arguments to this meta-variable are all binder variables, and are substituted to distinct
   * binder variables.  If any of the arguments violates this restriction, a
   * PatternRequiredException is thrown.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullPointerException("argument term for MetaApplication::match");
    if (gamma == null) throw new NullPointerException("substitution for MetaApplication::match");
    // get all the substituted arguments, and make sure they are distinct bound variables
    ArrayList<Variable> substitutedArgs = new ArrayList<Variable>();
    TreeSet<Variable> set = new TreeSet<Variable>();
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).isVariable()) throw new PatternRequiredException(toString(), "match",
        "argument " + (i+1) + " (" + _args.get(i) + ") is not a variable.");
      Variable x = _args.get(i).queryVariable();
      if (!x.isBinderVariable()) throw new PatternRequiredException(toString(), "match",
        "argument " + (i+1) + " ( " + x.toString() + ") is not a binder variable.");
      Term replacement = gamma.get(x);
      if (replacement == null) throw new PatternRequiredException(toString(), "match",
        "argument " + (i+1) + " ( " + x.toString() + ") is not bound above " + toString() + ".");
      if (!replacement.isVariable()) throw new PatternRequiredException(toString(), "match",
        "argument " + (i+1) + " ( " + x.toString() + ") is substituted to " +
        replacement.toString() + " in the context, which is not a variable.");
      Variable y = replacement.queryVariable();
      if (!y.isBinderVariable()) throw new PatternRequiredException(toString(), "match",
        "argument " + (i+1) + " ( " + x.toString() + ") is substituted to " +
        y.toString() + " in the context, which is a non-binder variable.");
      substitutedArgs.add(y);
      if (set.contains(y)) throw new PatternRequiredException(toString(), "match",
        "duplicate argument to meta-variable: argument " + (i+1) + " ( " + x.toString() + ") is " +
        "substituted to " + y.toString() + " which occurred before.");
      set.add(y);
    }
    // create abstraction
    Term ret = other;
    for (int i = substitutedArgs.size()-1; i >= 0; i--) {
      ret = new Abstraction(substitutedArgs.get(i), ret);
    }
    // check if the type matches (and perhaps a previous match), and add the mapping!
    Term previous = gamma.get(_metavar);
    if (previous == null) {
      if (!other.queryType().equals(queryType())) {
        return "Cannot match " + toString() + " against " + other.toString() + " as types do not " +
          "match.";
      }
      gamma.extend(_metavar, ret);
      return null;
    }
    else if (previous.equals(ret)) return null;
    else return "Meta-variable " + _metavar.toString() + " is mapped to both " +
      previous.toString() + " and to " + ret.toString() + ".";
  }

  /**
   * This method verifies equality to another Term.  Since meta-variables are not renamable
   * variables, a meta-application Z⟨s1,...,sk⟩ can only be equivalent to Z⟨t1,...,tk⟩ if each
   * si is α-equal to ti.
   */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isMetaApplication()) return false;
    if (!_metavar.equals(term.queryMetaVariable())) return false;
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).alphaEquals(term.queryMetaArgument(i+1), mu, xi, k)) return false;
    }
    return true;
  }

  /** This method returns a hashCode that maps alpha-equal terms to the same code. */
  public int hashCode(Map<Variable,Integer> mu) {
    int ret = _metavar.hashCode();
    for (int i = 0; i < _args.size(); i++) ret = 31 * ret + _args.get(i).hashCode(mu);
    return ret;
  }
}

