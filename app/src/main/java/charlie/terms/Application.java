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
import java.util.TreeMap;

import charlie.util.NullStorageException;
import charlie.util.Pair;
import charlie.types.Arrow;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.position.*;
import charlie.terms.replaceable.ReplaceableSet;

/** An Application is a term of the form h(s1,...,sn) where h is not an application. */
class Application extends TermInherit {
  public final Term _head;
  public final ArrayList<Term> _args;
  public final Type _outputType;

  //  Construction Phase ------------------------------------------------------

  /**
   * Helper function for the constructors: given the head and arguments, this checks that the
   * typing is correct, and returns the output type if so (if not, an appropriate TypingException
   * is thrown).
   */
  private Type checkType(Term head, List<Term> args) {
    Type type = head.queryType();
    for (int i = 0; i < args.size(); i++) {
      Term arg = args.get(i);
      if (arg == null) {
        throw new NullStorageException("Application", "passing a null argument to " + head + ".");
      }
      if (type instanceof Arrow(Type inp, Type out)) {
        if (!inp.equals(arg.queryType())) {
          throw new TypingException("Could not construct application headed by ", head, ": " +
            "argument " + (i + 1) + " of the head has type ", inp, " while the given argument to " +
            "be applied, ", arg, ", has type ", arg.queryType(), ".");
        }
        type = out;
      }
      else {
        throw new TypingException("Could not construct application headed by ", head, " with " +
          args.size() + " arguments: the head has type " + head.queryType(), ", which only " +
          "permits " + i + " arguments!");
      }
    }
    return type;
  }

  /**
   * Sets up the lists of free, bound and meta-variables used in this term, and builds _args from
   * the given set args (perhaps renaming bound variables in some of them).
   * Meant for use in the constructors, so it cannot use the freeReplaceables() function, but
   * rather, sets up the result of that function.
   * This assumes that _outputType and _args have already been set, and returns the value for _head.
   */
  private Term setupReplaceables(Term head, List<Term> args) {
    ReplaceableSet frees =
      calculateFreeReplaceablesForSubterms(args, head.queryFreeReplaceables());
    ReplaceableSet bounds = head.queryBoundVars();
    if (bounds.size() > 0 && !bounds.getOverlap(frees).isEmpty()) {
      head = head.renameAndRefreshBinders(new TreeMap<Variable,Variable>());
      bounds = head.queryBoundVars();
    }
    bounds = calculateBoundVariablesAndRefreshSubs(args, bounds, frees, _args);
    setVariables(frees, bounds,
                 calculateTypeVariablesForSubterms(args, head.queryTypeVars()));
    return head;
  }

  /**
   * This constructor is used to create a term which takes one argument.
   * Throws an error if the head is null or does not have arity ≥ 1, or the argument is null.
   */
  Application(Term head, Term arg) {
    this(head, List.of(arg));
  }

  /**
   * This constructor is used to create a term which takes two arguments.
   * Throws an error if the head does not have arity ≥ 2, or one of the arguments is null.
   */
  Application(Term head, Term arg1, Term arg2) {
    this(head, List.of(arg1, arg2));
  }

  /**
   * This constructor is used to create a term head(s1,...,sn) with n > 0.
   * Throws an exception if n does not match the arity of the head, if args is empty or or if the
   * types of the arguments are not the expected input types of the head.
   */
  Application(Term head, List<Term> args) {
    if (args.isEmpty()) {
      throw new IllegalArgumentException("Application::constructor --  creating an " +
        "Application with no arguments.");
    }
    _outputType = checkType(head, args);
    if (head.isApplication()) {
      ArrayList<Term> newArgs = head.listArguments();
      head = head.queryHead();
      newArgs.addAll(args);
      args = newArgs;
    }
    _args = new ArrayList<Term>();
    _head = setupReplaceables(head, args);
  }

  //  Main functionality ------------------------------------------------------

  /** This method returns the output type of the term. */
  @Override
  public Type queryType() {
    return _outputType;
  }

  /** @return true, since the current term is an application. */
  @Override
  public boolean isApplication() {
    return true;
  }

  /** Returns whether the head of this application is a function symbol. */
  @Override
  public boolean isFunctionalTerm() {
    return _head.isConstant();
  }

  /** Returns whether the head of this application is a variable. */
  @Override
  public boolean isVarTerm() {
    return _head.isVariable();
  }

  /** Returns whether the head of this application is an abstraction. */
  @Override
  public boolean isBetaRedex() {
    return _head.isAbstraction();
  }

  /** Adds all function symbols in the present term to storage. */
  @Override
  public void storeFunctionSymbols(Set<FunctionSymbol> storage) {
    _head.storeFunctionSymbols(storage);
    for (Term t : _args) t.storeFunctionSymbols(storage);
  }
  
  /** For a term h(s1,...,sn), this returns n. */
  public int queryNumberArguments() {
    return _args.size();
  }

  /** For a term h(s1,...,sn), this returns h.numberMetaArguments(). */
  public int queryNumberMetaArguments() {
    return _head.queryNumberMetaArguments();
  }

  /** Returns the list of all arguments, so [s1,...,sn] for h(s1,...,sn). */
  public ArrayList<Term> listArguments() {
    return new ArrayList<Term>(_args);
  }

  /** Returns the list of meta-arguments of the head. */
  public ArrayList<Term> listMetaArguments() {
    return _head.listMetaArguments();
  }

  /**
   * For a term head(s1,...,sn), this returns si if 1 <= i <= n, and throws an exception
   * otherwise.
   */
  public Term queryArgument(int i) {
    if (i <= 0 || i > _args.size()) {
      throw new IndexOutOfBoundsException("Application::queryArgument(" + i + ") called on " +
        "application with " + _args.size() + " arguments. (" + this + ")");
    }
    return _args.get(i-1);
  }

  /** For a term Z⟨t1,...,tk⟩(s1,...,sn), this returns ti, provided 1 ≤ i ≤ k. */
  public Term queryMetaArgument(int i) {
    return _head.queryMetaArgument(i);
  }

  /** For a term h(s1,...,sn) this returns h(s1,...,si). */
  public Term queryImmediateHeadSubterm(int i) {
    if (i < 0 || i > _args.size()) {
      throw new IndexOutOfBoundsException("Application::queryImmediateHeadSubterm(" + i + ") " +
        "called on application with " + _args.size() + " arguments (" + this + ")");
    }
    if (i == 0) return _head;
    return new Application(_head, _args.subList(0, i));
  }

  /** Returns the abstraction-subterm of the head (if head is an abstraction) */
  public Term queryAbstractionSubterm() {
    return _head.queryAbstractionSubterm();
  }

  /** @return the head of the application. */
  public Term queryHead() {
    return _head;
  }

   /** @return the root symbol of the head. */
  public FunctionSymbol queryRoot() {
    return _head.queryRoot();
  }

  /** @return the variable of the head. */
  public Variable queryVariable() {
    return _head.queryVariable();
  }

  /** @return the meta-variable of the head. */
  public MetaVariable queryMetaVariable() {
    return _head.queryMetaVariable();
  }

  /**
   * Returns true if this application is a functional term whose arguments are all first-order
   * terms, and the output type is a sort of type order 0.
   */
  public boolean isFirstOrder() {
    return _head.isConstant() &&
      _outputType.isZeroSort() &&
      _args.stream().allMatch(Term::isFirstOrder);
  }

  /**
   * Returns true if this application is a functional term, or variable term whose variable
   * is a binder, and the arguments are all patterns.
   */
  public boolean isPattern() {
    if (!_head.isConstant() && !_head.isVariable()) return false;
    if (_head.isVariable() && !_head.queryVariable().isBinderVariable()) return false;
    return _args.stream().allMatch(Term::isPattern);
  }

  /**
   * Returns true if this application is a semi-pattern; that is, that its head and all its
   * arguments are.
   */
  public boolean isSemiPattern() {
    if (!_head.isSemiPattern()) return false;
    return _args.stream().allMatch(Term::isSemiPattern);
  }

  /** Returns true if all strict subterms are applicative. */
  public boolean isApplicative() {
    if (!_head.isApplicative()) return false;
    return _args.stream().allMatch(Term::isApplicative);
  }

  /**
   * Returns the full subterms and their positions of this term, from left to right, followed by
   * the empty position.
   */
  public List<Pair<Term,Position>> listSubterms() {
    List<Pair<Term,Position>> ret = _head.listSubterms();
    ret.removeLast(); // remove the empty position
    for (int i = 0; i < _args.size(); i++) {
      List<Pair<Term,Position>> subposses = _args.get(i).listSubterms();
      for (Pair<Term, Position> pair : subposses) {
        ret.add(new Pair<Term, Position>(pair.fst(),
          new ArgumentPos(i + 1, pair.snd())));
      }
    }
    ret.add(new Pair<Term,Position>(this, Position.empty));
    return ret;
  }

  /** @return the subterm at the given (non-empty) position */
  public Term querySubtermMain(Position pos) {
    return switch (pos) {
      case FinalPos(int k) -> {
        if (k > _args.size()) {
          throw new InvalidPositionException(this, pos,
            "querying subterm with excessive chop count in application");
        }
        yield _head.apply(_args.subList(0, _args.size() - k));
      }
      case ArgumentPos(int index, Position tail) -> {
        if (index > _args.size()) {
          throw new InvalidPositionException(this, pos,
            "querying subterm in non-existing argument of application");
        }
        yield _args.get(index - 1).querySubterm(tail);
      }
      default -> _head.querySubterm(pos);
    };
  }

  /**
   * @return a copy of the term with the subterm at the given (non-empty) position replaced by
   * replacement, if such a position exists; otherwise throws an InvalidPositionException.
   */
  public Term replaceSubtermMain(Position pos, Term replacement) {
    switch (pos) {
      case FinalPos(int k):
        if (k > _args.size()) {
          throw new InvalidPositionException(this, pos,
            "replacing subterm with excessive chop count in application");
        }
        Type type = queryType();
        for (int i = 1; i <= k; i++) {
          type = TypeFactory.createArrow(_args.get(_args.size()-i).queryType(), type);
        }
        if (!type.equals(replacement.queryType())) {
          Term t = k == 0 ? this : k == _args.size() ? _head
                          : new Application(_head, _args.subList(0, _args.size()-k));
          throw new TypingException("Typing error when replacing a subterm: I cannot replace ", t,
            " by ", replacement, " since the former has type ", type, " while the latter has type ",
            replacement.queryType(), ".");
        }
        return replacement.apply(_args.subList(_args.size()-k, _args.size()));
      case ArgumentPos(int index, Position tail):
        if (index > _args.size()) {
          throw new InvalidPositionException(this, pos,
            "replacing subterm in non-existing argument of application");
        }
        Term tmp = _args.get(index-1);
        _args.set(index-1, tmp.replaceSubterm(tail, replacement));
        Term ret = new Application(_head, _args);
        _args.set(index-1, tmp);
        return ret;
      default:
        Term newhead = _head.replaceSubterm(pos, replacement);
        return new Application(newhead, _args);
    }
  }

  /**
   * This method yields a copy with all binders in the renaming's mapping renamed, and the
   * binders in lambdas below this term refreshed.
   */
  public Term renameAndRefreshBinders(Map<Variable,Variable> renaming) {
    Term head = _head.renameAndRefreshBinders(renaming);
    ArrayList<Term> args = new ArrayList<Term>(_args);
    boolean changed = head != _head;
    for (int i = 0; i < args.size(); i++) {
      Term other = args.get(i).renameAndRefreshBinders(renaming);
      if (other != args.get(i)) {
        changed = true;
        args.set(i, other);
      }   
    }   
    if (!changed) return this;
    return new Application(head, args);
  }

  /** This method verifies equality to another Term. */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isApplication()) return false;
    if (!_head.alphaEquals(term.queryHead(), mu, xi, k)) return false;
    if (_args.size() != term.queryNumberArguments()) return false;
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).alphaEquals(term.queryArgument(i+1), mu, xi, k)) return false;
    }
    return true;
  }

  /** This method returns a hashCode that maps alpha-equal terms to the same code. */
  public int hashCode(Map<Variable,Integer> mu) {
    int ret = _head.hashCode(mu);
    for (Term arg : _args) ret = 31 * ret + arg.hashCode(mu);
    return ret;
  }
}
