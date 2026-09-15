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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import charlie.util.Pair;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.terms.position.Position;
import charlie.terms.position.MetaPos;
import charlie.terms.replaceable.ReplaceableSet;

/**
 * A MetaApplication is a term of the form Z⟨s1,...,sk⟩ where Z is a meta-variable with arity
 * k ≥ 1.  MetaApplications of the form Z⟨⟩ are viewed as non-binder variables, so should be
 * created as a Var instead.
 */
class MetaApplication extends TermInherit {
  public final MetaVariable _metavar;
  public final ArrayList<Term> _args;

  /**
   * This constructor is used to create a term mvar⟨s1,...,sk⟩ with k ≥ 1.
   * Throws an error if k does not match the arity of the meta-variable, if args is empty or if the
   * types of the arguments are not the expected input types of the meta-variable.
   */
  MetaApplication(MetaVariable mvar, List<Term> args) {
    if (mvar == null) throw new NullStorageException("MetaApplication", "meta-variable");
    _metavar = mvar;
    
    if (args.isEmpty()) {
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
      if (!arg.queryType().equals(mvar.queryInputType(i+1))) {
        throw new TypingException("Typing error constructing meta-variable application: " +
          "imput type " + (i+1) + " of meta-variable ", mvar, " is ", mvar.queryInputType(i+1) +
          ", while the argument term ", arg, " has type ", arg.queryType());
      }
    }
    _args = new ArrayList<Term>();
    ReplaceableSet empty = ReplaceableSet.EMPTY;
    ReplaceableSet start = new ReplaceableSet(_metavar);
    ReplaceableSet frees = calculateFreeReplaceablesForSubterms(args, start);
    ReplaceableSet bounds = calculateBoundVariablesAndRefreshSubs(args, empty, frees, _args);
    setVariables(frees, bounds, calculateTypeVariablesForSubterms(args, mvar.queryTypeVars()));
  }

  /** @return the output type of the meta-variable. */
  @Override
  public Type queryType() {
    return _metavar.queryOutputType();
  }

  @Override
  public boolean isMetaApplication() {
    return true;
  }

  @Override
  public boolean isApplicative() {
    return false;
  }

  @Override
  public boolean isFirstOrder() {
    return false;
  }

  /** Adds all function symbols in the present term to storage. */
  @Override
  public void storeFunctionSymbols(Set<FunctionSymbol> storage) {
    for (Term t : _args) t.storeFunctionSymbols(storage);
  }

  /** @return the number of meta-arguments */
  @Override
  public int queryNumberMetaArguments() {
    return _args.size();
  }

  /** @return the list of meta-arguments */
  @Override
  public ArrayList<Term> listMetaArguments() {
    return new ArrayList<Term>(_args);
  }

  /** If this term is Z⟨s1,...,sk⟩, returns si. */
  @Override
  public Term queryMetaArgument(int i) {
    if (i <= 0 || i > _args.size()) {
      throw new IndexOutOfBoundsException("MetaApplication::queryMetaArgument(" + i + ") called " +
        "on meta-variable application with " + _args.size() + " arguments.");
    }
    return _args.get(i-1);
  }

  /** @throws InappropriatePatternDataException since a meta-variable is not a variable */
  @Override
  public Variable queryVariable() {
    throw new InappropriatePatternDataException("MetaApplication", "queryVariable",
      "var terms or abstractions");
  }

  /** @return the metavariable for this meta-application */
  @Override
  public MetaVariable queryMetaVariable() {
    return _metavar;
  }

  /** Returns true if this meta-application is applied to distinct binder variables. */
  @Override
  public boolean isPattern() {
    if (queryFreeReplaceables().size() != _args.size() + 1) return false;
    for (Term arg : _args) {
      if (!arg.isVariable()) return false;
      if (!arg.queryVariable().isBinderVariable()) return false;
    }
    return true;
  }

  /** Returns true if this meta-application is applied to distinct binder variables. */
  @Override
  public boolean isSemiPattern() {
    return isPattern();
  }

  /**
   * Returns all full subterms and their respective positions, from left to right, with the current
   * term and empty position in the end.
   */
  @Override
  public List<Pair<Term,Position>> listSubterms() {
    List<Pair<Term,Position>> ret = new ArrayList<Pair<Term,Position>>();
    for (int i = 0; i < _args.size(); i++) {
      List<Pair<Term,Position>> subs = _args.get(i).listSubterms();
      for (Pair<Term, Position> sub : subs) {
        ret.add(new Pair<Term, Position>(sub.fst(), new MetaPos(i + 1, sub.snd())));
      }
    }
    ret.add(new Pair<Term,Position>(this, Position.empty));
    return ret;
  }

  /** @return the subterm at the given (non-empty) position */
  @Override
  public Term querySubtermMain(Position pos) {
    if (pos instanceof MetaPos(int index, Position tail)) {
      if (index <= _args.size()) return _args.get(index - 1).querySubterm(tail);
    }
    throw new InvalidPositionException(this, pos, "querying subterm of meta-application");
  }

  /**
   * @return a copy of the term with the subterm at the given (non-empty) position replaced by
   * replacement, if such a position exists; otherwise throws an InvalidPositionException.
   */
  @Override
  public Term replaceSubtermMain(Position pos, Term replacement) {
    if (pos instanceof MetaPos(int index, Position tail)) {
      if (index <= _args.size()) {
        Term tmp = _args.get(index - 1);
        _args.set(index - 1, tmp.replaceSubterm(tail, replacement));
        Term ret = new MetaApplication(_metavar, _args);
        _args.set(index - 1, tmp);
        return ret;
      }
    }
    throw new InvalidPositionException(this, pos, "replacing subterm of meta-application");
  }

  /**
   * This method constructs a copy of the current meta-application, where the binder variables are
   * renamed using renaming, and all lambdas also have their binders refreshed.
   */
  @Override
  public Term renameAndRefreshBinders(Map<Variable,Variable> renaming) {
    ArrayList<Term> args = null;
    for (int i = 0; i < _args.size(); i++) {
      Term other = _args.get(i).renameAndRefreshBinders(renaming);
      if (other != _args.get(i)) {
        if (args == null) args = new ArrayList<Term>(_args);
        args.set(i, other);
      }
    }
    if (args == null) return this;
    return new MetaApplication(_metavar, args);
  }

  /**
   * This method verifies equality to another Term.  Since meta-variables are not renamable
   * variables, a meta-application Z⟨s1,...,sk⟩ can only be equivalent to Z⟨t1,...,tk⟩ if each
   * si is α-equal to ti.
   */
  @Override
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu,
                             Map<Variable,Integer> xi, int k) {
    if (!term.isMetaApplication()) return false;
    if (!_metavar.equals(term.queryMetaVariable())) return false;
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).alphaEquals(term.queryMetaArgument(i+1), mu, xi, k)) return false;
    }
    return true;
  }

  /** This method returns a hashCode that maps alpha-equal terms to the same code. */
  @Override
  public int hashCode(Map<Variable,Integer> mu) {
    int ret = _metavar.hashCode();
    for (int i = 0; i < _args.size(); i++) ret = 31 * ret + _args.get(i).hashCode(mu);
    return ret;
  }
}
