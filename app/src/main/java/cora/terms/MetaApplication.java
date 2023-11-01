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
import java.util.TreeSet;
import cora.exceptions.*;
import cora.types.Type;

/**
 * A MetaApplication is a term of the form Z⟨s1,...,sk⟩ where Z is a meta-variable with arity
 * k ≥ 1.  MetaApplications of the form Z⟨⟩ are viewed as non-binder variables, so should be
 * created as a Var instead.
 */
class MetaApplication extends TermInherit {
  public MetaVariable _metavar;
  public List<Term> _args;

  /**
   * This constructor is used to create a term mvar⟨s1,...,sk⟩ with k ≥ 1.
   * Throws an error if k does not match the arity of the meta-variable, if args is empty or if the
   * types of the arguments are not the expected input types of the meta-variable.
   */
  MetaApplication(MetaVariable mvar, List<Term> args) {
    if (mvar == null) throw new NullInitialisationError("MetaApplication", "meta-variable");
    if (args == null) throw new NullInitialisationError("MetaApplication", "argument list");
    _metavar = mvar;
    
    if (args.size() == 0) {
      throw new IllegalTermError("MetaApplication", "creating a MetaApplication with no " +
        "arguments: this should be done through the Var class, since a meta-application " +
        "without arguments is just a non-binder variable.");
    }
    if (args.size() != mvar.queryArity()) {
      throw new ArityError("MetaApplication", "constructor", "meta-variable " + mvar.queryName() +
        " has arity " + mvar.queryArity() + " but " + args.size() + " arguments are given.");
    }
    _args = new ArrayList<Term>(args);

    for (int i = 0; i < args.size(); i++) {
      Term arg = args.get(i);
      if (arg == null) {
        throw new NullInitialisationError("MetaApplication", "passing a null argument to " +
          "meta-variable application for " + mvar.queryName() + ".");
      }
      if (!arg.queryType().equals(mvar.queryInputType(i+1))) {
        throw new TypingError("MetaApplication", "constructor", "arg " + (i+1) + " of " +
          mvar.toString(), arg.queryType().toString(), mvar.queryInputType(i+1).toString());
      }
    }
    ReplaceableList empty = ReplaceableList.EMPTY;
    ReplaceableList start = new ReplaceableList(_metavar);
    ReplaceableList frees = calculateFreeReplaceablesForSubterms(_args, start);
    ReplaceableList bounds = calculateBoundVariablesAndRefreshSubs(_args, empty, frees);
    setVariables(frees, bounds);
  }

  /** @return the output type of the meta-variable. */
  public Type queryType() {
    return _metavar.queryOutputType();
  }

  public boolean isConstant() {
    return false;
  }

  public boolean isVariable() {
    return false;
  }

  public boolean isAbstraction() {
    return false;
  }

  public boolean isMetaApplication() {
    return true;
  }

  public boolean isApplication() {
    return false;
  }

  public boolean isApplicative() {
    return false;
  }

  public boolean isFirstOrder() {
    return false;
  }

  public boolean isFunctionalTerm() {
    return false;
  }

  public boolean isVarTerm() {
    return false;
  }

  public boolean isBetaRedex() {
    return false;
  }

  public boolean isTheoryTerm() {
    if (!_metavar.queryType().isTheoryType()) return false;
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).isTheoryTerm()) return false;
    }
    return true;
  }

  public boolean isValue() {
    return false;
  }

  public Value toValue() {
    return null;
  }

  /** @return 0, since a meta-application does not have arguments */
  public int numberArguments() {
    return 0;
  }

  /** @return the number of meta-arguments */
  public int numberMetaArguments() {
    return _args.size();
  }

  /** Returns the empty list. */
  public List<Term> queryArguments() {
    return new ArrayList<Term>();
  }

  /** @throws IndexingError, as a meta-application does not have arguments. */
  public Term queryArgument(int i) {
    throw new IndexingError("MetaApplication", "queryArgument", i);
  }

  /** If this term is Z⟨s1,...,sk⟩, returns si. */
  public Term queryMetaArgument(int i) {
    if (i <= 0 || i > _args.size()) {
      throw new IndexingError("MetaApplication", "queryMetaArgument", i, 1, _args.size());
    }
    return _args.get(i-1);
  }

  /** Either returns this (if i == 0) or throws an IndexingError. */
  public Term queryImmediateHeadSubterm(int i) {
    if (i == 0) return this;
    throw new IndexingError("MetaApplication", "queryImmediateHeadSubterm", i);
  }

  /** @throws InappropriatePatternDataError */
  public Term queryAbstractionSubterm() {
    throw new InappropriatePatternDataError("MetaApplication", "queryAbstractionSubterm",
      "abstractions or beta-redexes");
  }

  /** @return this */
  public Term queryHead() {
    return this;
  }

  /** @throws InappropriatePatternDataError */
  public FunctionSymbol queryRoot() {
    throw new InappropriatePatternDataError("MetaApplication", "queryRoot",
      "functional terms");
  }

  /** @throws InappropriatePatternDataError */
  public Variable queryVariable() {
    throw new InappropriatePatternDataError("MetaApplication", "queryVariable",
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

  /**
   * Returns the non-head positions in all subterms, from left to right, followed by the empty
   * position.
   */
  public List<Path> queryPositions() {
    List<Path> ret = queryPositionsForHead(this);
    ret.add(new EmptyPath(this));
    return ret;
  }

  /** 
   * @return the list of all non-root positions in this term, in innermost-left order; however,
   *   the associated term is set to top rather than the current term
   */
  public List<Path> queryPositionsForHead(Term top) {
    ArrayList<Path> ret = new ArrayList<Path>();
    for (int i = 0; i < _args.size(); i++) {
      List<Path> subposses = _args.get(i).queryPositions();
      for (int j = 0; j < subposses.size(); j++) {
        ret.add(new MetaPath(top, i+1, subposses.get(j)));
      }   
    }   
    return ret;
  }

  /** @return this if the position is empty; otherwise the position in the given subterm */
  public Term querySubterm(Position pos) {
    if (pos.isEmpty()) return this;
    if (!pos.isMeta()) throw new IndexingError("MetaApplication", "querySubterm", toString(),
      pos.toString());
    int index = pos.queryMetaPosition();
    if (index < 1 || index > _args.size()) {
      throw new IndexingError("MetaApplication", "querySubterm", toString(), pos.toString());
    }
    return _args.get(index-1).querySubterm(pos.queryTail());
  }

  /**
   * @return a copy of the term with the subterm at the given position replaced by replacement, if
   * such a position exists; otherwise throws an IndexingError.
   */
  public Term replaceSubterm(Position pos, Term replacement) {
    return replaceSubterm(new HeadPosition(pos), replacement);
  }

  /**
   * @return a copy of the term with the subterm at the given head position replaced by
   * replacement, if such a position exists; otherwise throws an IndexingError.
   */
  public Term replaceSubterm(HeadPosition pos, Term replacement) {
    if (pos.isEnd()) {
      if (pos.queryChopCount() != 0) {
        throw new IndexingError("MetaApplication", "replaceSubterm", toString(), pos.toString());
      }
      else if (!queryType().equals(replacement.queryType())) {
        throw new TypingError("MetaApplication", "replaceSubterm", "replacement term " +
                    replacement.toString(), replacement.queryType().toString(),
                    queryType().toString());
      }
      else return replacement;
    }

    if (!pos.isMeta()) {
      throw new IndexingError("MetaApplication", "replaceSubterm", toString(), pos.toString());
    }

    int index = pos.queryMetaPosition();
    if (index < 1 || index > _args.size()) {
      throw new IndexingError("MetaApplication", "replaceSubterm", toString(), pos.toString());
    }   
    Term tmp = _args.get(index-1);
    _args.set(index-1, tmp.replaceSubterm(pos.queryTail(), replacement));
    Term ret = new MetaApplication(_metavar, _args);
    _args.set(index-1, tmp);
    return ret;
  }

  /**
   * This method replaces each variable x in the term by gamma(x) (or leaves x alone if x is not
   * in the domain of gamma), and each meta-application Z[s1,...,sk] with γ(Z) = λx1...xk.t by
   * t[x1:=s1γ,...,xk:=skγ]; the result is returned.
   */
  public Term substitute(Substitution gamma) {
    if (gamma == null) throw new NullCallError("Application", "substitute", "substitution (gamma)");
    ArrayList<Term> newArgs = new ArrayList<Term>();
    for (int i = 0; i < _args.size(); i++) newArgs.add(_args.get(i).substitute(gamma));
    Term value = gamma.get(_metavar);
    if (value == null) return new MetaApplication(_metavar, newArgs);
    Substitution delta = new Subst();
    Term v = value;
    for (int i = 0; i < newArgs.size(); i++) {
      if (!v.isAbstraction()) {
        throw new ArityError("MetaApplication", "substitute", "trying to substitute " +
          "meta-variable in " + toString() + " by " + value.toString() +
          ": there should be " + newArgs.size() + " abstractions!");
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
   * binder variables.  If any of the arguments violates this restriction, a PatternRequiredError
   * is thrown.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("Application", "match", "argument term (other)");
    if (gamma == null) throw new NullCallError("Application", "match", "substitution (gamma)");
    // get all the substituted arguments, and make sure they are distinct bound variables
    ArrayList<Variable> substitutedArgs = new ArrayList<Variable>();
    TreeSet<Variable> set = new TreeSet<Variable>();
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).isVariable()) throw new PatternRequiredError(toString(), "match",
        "argument " + (i+1) + " (" + _args.get(i) + ") is not a variable.");
      Variable x = _args.get(i).queryVariable();
      if (!x.isBinderVariable()) throw new PatternRequiredError(toString(), "match",
        "argument " + (i+1) + " ( " + x.toString() + ") is not a binder variable.");
      Term replacement = gamma.get(x);
      if (replacement == null) throw new PatternRequiredError(toString(), "match",
        "argument " + (i+1) + " ( " + x.toString() + ") is not bound above " + toString() + ".");
      if (!replacement.isVariable()) throw new PatternRequiredError(toString(), "match",
        "argument " + (i+1) + " ( " + x.toString() + ") is substituted to " +
        replacement.toString() + " in the context, which is not a variable.");
      Variable y = replacement.queryVariable();
      if (!y.isBinderVariable()) throw new PatternRequiredError(toString(), "match",
        "argument " + (i+1) + " ( " + x.toString() + ") is substituted to " +
        y.toString() + " in the context, which is a non-binder variable.");
      substitutedArgs.add(y);
      if (set.contains(y)) throw new PatternRequiredError(toString(), "match",
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

  /** This method gives a string representation of the term. */
  public void addToString(StringBuilder builder, Map<Replaceable,String> renaming,
                          Set<String> avoid) {
    if (renaming == null || !renaming.containsKey(_metavar)) builder.append(_metavar.queryName());
    else builder.append(renaming.get(_metavar));
    builder.append("⟨");
    _args.get(0).addToString(builder, renaming, avoid);
    for (int i = 1; i < _args.size(); i++) {
      builder.append(", ");
      _args.get(i).addToString(builder, renaming, avoid);
    }
    builder.append("⟩");
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
}

