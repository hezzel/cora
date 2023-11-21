/**************************************************************************************************
 Copyright 2023 Cynthia Kop

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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import cora.exceptions.*;
import cora.types.Type;
import cora.types.TypeFactory;

/** An Application is a term of the form h(s1,...,sn) where h is not an application. */
class Application extends TermInherit {
  public Term _head;
  public List<Term> _args;
  public Type _outputType;

//  Construction Phase --------------------------------------------------------
  /**
   * Sets up the lists of free, bound and meta-variables used in this term.
   * Meant for use in the constructors, so it cannot use the freeReplaceables() function, but
   * rather, sets up the result of that function.
   */
  private void setupReplaceables() {
    ReplaceableList frees = calculateFreeReplaceablesForSubterms(_args, _head.freeReplaceables());
    ReplaceableList bounds = _head.boundVars();
    if (bounds.size() > 0 && !bounds.getOverlap(frees).isEmpty()) {
      _head = _head.refreshBinders();
      bounds = _head.boundVars();
    }
    bounds = calculateBoundVariablesAndRefreshSubs(_args, bounds, frees);
    setVariables(frees, bounds);
  }

  /**
   * This helper function handles the functionality for the constructors to set up _head, _args
   * and _outputType, and store the variables and meta-variables.
   * If there are any problems -- such as the head or an argument being null, or the types not
   * checking out -- an appropriate Error is thrown. However, it *is* assumed that args is not
   * null.
   */
  private void construct(Term head, List<Term> args) {
    if (head == null) throw new NullInitialisationError("Application", "head");
    _head = head;
    
    if (_head.isApplication()) {
      _args = new ArrayList<Term>(head.queryArguments());
      _args.addAll(args);
      _head = _head.queryHead();
    }
    else _args = args;

    if (_args.size() == 0) {
      throw new IllegalArgumentError("Application", "constructor", "creating an Application " +
        "with no arguments.");
    }

    Type type = _head.queryType();
    for (int i = 0; i < _args.size(); i++) {
      Term arg = _args.get(i);
      if (arg == null) {
        throw new NullInitialisationError("Application", "passing a null argument to " +
          head.toString() + ".");
      }
      if (!type.isArrowType()) {
        throw new ArityError("Application", "constructor", "head term " + _head.toString() +
          " has maximum arity " + i + " and is given " + _args.size() + " arguments.");
      }
      Type input = type.queryArrowInputType();
      if (!input.equals(arg.queryType())) {
        throw new TypingError("Application", "constructor", "arg " + (i+1) + " of " +
          _head.toString(), arg.queryType() == null ? "null" : arg.queryType().toString(),
          input.toString());
      }
      type = type.queryArrowOutputType();
    }
    _outputType = type;
    setupReplaceables();
  }

  /**
   * This constructor is used to create a term which takes one argument.
   * Throws an error if the head is null or does not have arity ≥ 1, or the argument is null.
   */
  Application(Term head, Term arg) {
    List<Term> args = new ArrayList<Term>();
    args.add(arg);
    construct(head, args);
  }

  /**
   * This constructor is used to create a term which takes two arguments.
   * Throws an error if the head does not have arity ≥ 2, or one of the arguments is null.
   */
  Application(Term head, Term arg1, Term arg2) {
    List<Term> args = new ArrayList<Term>();
    args.add(arg1);
    args.add(arg2);
    construct(head, args);
  }

  /**
   * This constructor is used to create a term head(s1,...,sn) with n >= 0.
   * Throws an error if n does not match the arity of the head, if args is empty or or if the
   * types of the arguments are not the expected input types of the head.
   */
  Application(Term head, List<Term> args) {
    if (args == null) throw new NullInitialisationError("Application", "argument list");
    construct(head, new ArrayList<Term>(args));
  }


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

  /** Returns whether the head and all arguments are logical terms. */
  @Override
  public boolean isTheoryTerm() {
    return _head.isTheoryTerm() && _args.stream().allMatch(Term::isTheoryTerm);
  }
  
  /** @return null since an application is not a value. */
  public Value toValue() {
    return null;
  }

  /** For a term h(s1,...,sn), this returns n. */
  public int numberArguments() {
    return _args.size();
  }

  /** For a term h(s1,...,sn), this returns h.numberMetaArguments(). */
  public int numberMetaArguments() {
    return _head.numberMetaArguments();
  }

  /** Returns the list of all arguments, so [s1,...,sn] for h(s1,...,sn). */
  public List<Term> queryArguments() {
    return new ArrayList<Term>(_args);
  }

  /** For a term head(s1,...,sn), this returns si if 1 <= i <= n, and throws an error otherwise. */
  public Term queryArgument(int i) {
    if (i <= 0 || i > _args.size()) {
      throw new IndexingError("Application", "queryArgument", i, 1, _args.size());
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
      throw new IndexingError("Application", "queryImmediateHeadSubterm", i, 0, _args.size());
    }   
    if (i == 0) return _head;
    List<Term> newargs = new ArrayList<Term>();
    for (int j = 0; j < i; j++) newargs.add(_args.get(j));
    return new Application(_head, newargs);
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
   * terms, and the output type is a base type.
   */
  public boolean isFirstOrder() {
    return _head.isConstant() &&
      _outputType.isBaseType() &&
      _args.stream().allMatch(Term::isFirstOrder);
  }

  /**
   * Returns true if this application is a functional or variable term whose variable
   * is a binder,
   * and the arguments are all patterns.
   */
  public boolean isPattern() {
    if (!_head.isConstant() && !_head.isVariable()) return false;
    if (_head.isVariable() && !_head.queryVariable().isBinderVariable()) return false;
    return _args.stream().allMatch(Term::isPattern);
  }

  /** Returns true if all strict subterms are applicative. */
  public boolean isApplicative() {
    if (!_head.isApplicative()) return false;
    return _args.stream().allMatch(Term::isApplicative);
  }

  /**
   * Returns the non-head positions in all subterms, from left to right, followed by the empty
   * position.
   */
  public List<Path> queryPositions() {
    List<Path> ret = _head.queryPositionsForHead(this);
    for (int i = 0; i < _args.size(); i++) {
      List<Path> subposses = _args.get(i).queryPositions();
      for (int j = 0; j < subposses.size(); j++) {
        ret.add(new ArgumentPath(this, i+1, subposses.get(j)));
      }
    }
    ret.add(new EmptyPath(this));
    return ret;
  }

  /** Throws an error, since this should only be called on the head of top. */
  public List<Path> queryPositionsForHead(Term top) {
    throw new InappropriatePatternDataError("Application", "queryPositionsForHead",
      "head terms (which cannot be applications)");
  }

  /** @return this if the position is empty; otherwise the position in the given subterm */
  public Term querySubterm(Position pos) {
    if (pos.isEmpty()) return this;
    if (!pos.isArgument()) return _head.querySubterm(pos);
    int index = pos.queryArgumentPosition();
    if (index < 1 || index > _args.size()) {
      throw new IndexingError("Application", "querySubterm", toString(), pos.toString());
    }
    return _args.get(index-1).querySubterm(pos.queryTail());
  }

  /**
   * @return a copy of the term with the subterm at the given position replaced by replacement, if
   * such a position exists; otherwise throws an IndexingError.
   */
  public Term replaceSubterm(Position pos, Term replacement) {
    if (pos.isEmpty()) {
      if (!queryType().equals(replacement.queryType())) {
        throw new TypingError("Application", "replaceSubterm", "replacement term " +
                    replacement.toString(), replacement.queryType().toString(),
                    queryType().toString());
      }
      return replacement;
    }
    if (!pos.isArgument()) {
      Term newhead = _head.replaceSubterm(pos, replacement);
      return new Application(newhead, _args);
    }
    int index = pos.queryArgumentPosition();
    if (index < 1 || index > _args.size()) {
      throw new IndexingError("Application", "replaceSubterm", toString(), pos.toString());
    }
    Term tmp = _args.get(index-1);
    _args.set(index-1, tmp.replaceSubterm(pos.queryTail(), replacement));
    Term ret = new Application(_head, _args);
    _args.set(index-1, tmp);
    return ret;
  }

  /**
   * @return a copy of the term with the subterm at the given head position replaced by
   * replacement, if such a position exists; otherwise throws an IndexingError.
   */
  public Term replaceSubterm(HeadPosition pos, Term replacement) {
    if (pos.isEnd()) {
      int chopcount = pos.queryChopCount();
      if (chopcount > _args.size()) {
        throw new IndexingError("Application", "replaceSubterm(HeadPosition)",
          toString(), pos.toString());
      }
      Type type = queryType();
      for (int i = 1; i <= chopcount; i++) {
        type = TypeFactory.createArrow(_args.get(_args.size()-i).queryType(), type);
      }
      if (!type.equals(replacement.queryType())) {
        throw new TypingError("Application", "replaceSubterm(HeadPosition)",
                    "replacement term " + replacement.toString(),
                    replacement.queryType().toString(), type.toString());
      }
      return replacement.apply(_args.subList(_args.size()-chopcount, _args.size()));
    }
    if (!pos.isArgument()) {
      Term newhead = _head.replaceSubterm(pos, replacement);
      return new Application(newhead, _args);
    }
    int index = pos.queryArgumentPosition();
    if (index < 1 || index > _args.size()) {
      throw new IndexingError("Application", "replaceSubterm(HeadPosition)", toString(),
        pos.toString());
    }
    Term tmp = _args.get(index-1);
    _args.set(index-1, tmp.replaceSubterm(pos.queryTail(), replacement));
    Term ret = new Application(_head, _args);
    _args.set(index-1, tmp);
    return ret;
  }

  /**
   * This method replaces each variable x in the term by gamma(x) (or leaves x alone if x is not
   * in the domain of gamma); the result is returned.
   */
  public Term substitute(Substitution gamma) {
    Term h = _head.substitute(gamma);
    if (h == null) throw new Error("Substituting " + _head.toString() + " results in null!");

    List<Term> args = new ArrayList<Term>(_args);
    for (int i = 0; i < args.size(); i++) {
      Term t = args.get(i).substitute(gamma);
      if (t == null) {
        throw new Error("Substituting " + args.get(i).toString() + " results in null!");
      }
      args.set(i, t);
    }

    return new Application(h, args);
  }

  /**
   * This method either extends gamma so that <this term> gamma = other and returns null, or
   * returns a string describing why other is not an instance of gamma.
   * Whether null is returned, gamma is likely to be extended (although without overriding)
   * by this function.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("Application", "match", "argument term (other)");
    if (!other.isApplication()) {
      return other.toString() + " does not instantiate " + toString() + " (not an application).";
    }   
    if (other.numberArguments() < _args.size()) {
      return other.toString() + " does not instantiate " + toString() + " (too few arguments).";
    }   
    int i = other.numberArguments();
    int j = numberArguments();
    for (; j > 0; i--, j--) {
      Term mysub = queryArgument(j);
      Term hissub = other.queryArgument(i);
      String warning = mysub.match(hissub, gamma);
      if (warning != null) return warning;
    }   
    return _head.match(other.queryImmediateHeadSubterm(i), gamma);
  }

  /** This method gives a string representation of the term. */
  public void addToString(StringBuilder builder, Map<Replaceable,String> renaming,
                          Set<String> avoid) {
    // special case for a theory term
    if (_head.isConstant()) {
      CalculationSymbol f = _head.queryRoot().toCalculationSymbol();
      if (f != null && f.printInfix(builder, _args, renaming, avoid)) return;
    }

    if (_head.isAbstraction()) builder.append("(");
    _head.addToString(builder, renaming, avoid);
    if (_head.isAbstraction()) builder.append(")");
    builder.append("(");
    _args.get(0).addToString(builder, renaming, avoid);
    for (int i = 1; i < _args.size(); i++) {
      builder.append(", ");
      _args.get(i).addToString(builder, renaming, avoid);
    }
    builder.append(")");
  }

  /** This method verifies equality to another Term. */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isApplication()) return false;
    if (!_head.alphaEquals(term.queryHead(), mu, xi, k)) return false;
    if (_args.size() != term.numberArguments()) return false;
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).alphaEquals(term.queryArgument(i+1), mu, xi, k)) return false;
    }
    return true;
  }
}
