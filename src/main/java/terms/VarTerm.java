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

package cora.terms;

import java.util.List;
import java.util.ArrayList;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.IndexingError;
import cora.exceptions.NullCallError;
import cora.exceptions.UnexpectedPatternError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;

/**
 * VarTerms are terms of the form x(s1,...,sn) where s1,...,sn are all terms and x is a variable.
 * Here, n may be 0, but both n and the types of s1,...,sn are restricted by the type of x. 
 */
public class VarTerm extends ApplicativeTermInherit implements Term {
  private Variable _x;

  /**
   * This constructor is used to create a term which takes one argument.
   * Throws an error if the constant is null or does not have arity 1, or the argument is null.
   */
  public VarTerm(Variable x, Term arg) {
    super(x, arg);
    _x = x;
  }

  /**
   * This constructor is used to create a term which takes two arguments.
   * Throws an error if the constant does not have arity 2, or one of the arguments is null.
   */
  public VarTerm(Variable x, Term arg1, Term arg2) {
    super(x, arg1, arg2);
    _x = x;
  }

  /**
   * This constructor is used to create a term x(s1,...,sn) with n >= 0.
   * Throws an error if n does not match the arity of x, or if the types of the arguments are not
   * the expected input types of f.
   */
  public VarTerm(Variable x, List<Term> args) {
    super(x, args);
    _x = x;
  }

  /**
   * This constructor is used to create a term x(s1,...,sn) with n >= 0 and the given output type,
   * without any checks of for instance type correctness being done.
   * Moreover, the array list args becomes the property of the new term, and may not be modified
   * afterwards.
   * Only for features like substitution or simplifications. Be very careful using this!
   */
  private VarTerm(List<Term> args, Variable x, Type outputType) {
    _x = x;
    _head = x;
    _args = args;
    _outputType = outputType;
    initiateVars();
  }

  /** This method is called by inherited functions, and calls the private constructor. */
  protected VarTerm reconstruct(List<Term> args) {
    return new VarTerm(args, _x, _outputType);
  }

  /** @return true iff the number of arguments is 0 */
  public boolean isVariable() {
    return _args.size() == 0;
  }

  /** @return true */
  public boolean isVarTerm() {
    return true;
  }

  /** @return fakse */
  public boolean isConstant() {
    return false;
  }

  /** @return true */
  public boolean isFunctionalTerm() {
    return false;
  }

  /** @return false */
  public boolean isAbstraction() {
    return false;
  }

  /** Throws an error, because a varterm does not have a "root" function symbol. */
  public FunctionSymbol queryRoot() {
    throw new InappropriatePatternDataError("VarTerm", "queryRoot",
                                            "functional terms");
  }

  /** For a term x(s1,...,sn), this returns x. */
  public Variable queryVariable() {
    return _x;
  }

  /** For a term x(s1,...,sn), this returns x(s1,...,si). */
  public Term queryImmediateHeadSubterm(int i) {
    if (i < 0 || i > _args.size()) {
      throw new IndexingError("VarTerm", "queryImmediateHeadSubterm", i, 0, _args.size());
    }
    if (i == 0) return _x;
    List<Term> newargs = new ArrayList<Term>();
    for (int j = 0; j < i; j++) newargs.add(_args.get(j));
    return new VarTerm(_x, newargs);
  }

  /**
   * Returns true only if this is a first-order variable.
   * (A true application is by definition not a first-order term.)
   */
  public boolean isFirstOrder() {
    return _args.size() == 0 && _x.isFirstOrder();
  }

  /**
   * Returns true if this is either a bound variable applied to patterns, or a free variable
   * applied to distinct bound variables.
   */
  public boolean isPattern() {
    if (_x.isBinderVariable()) {
      for (int i = 0; i < _args.size(); i++) {
        if (!_args.get(i).isPattern()) return false;
      }
      return true;
    }
    else {
      for (int i = 0; i < _args.size(); i++) {
        if (!_args.get(i).isVariable()) return false;
        Variable x = (Variable)_args.get(i);
        if (!x.isBinderVariable()) return false;
        for (int j = i+1; j < _args.size(); j++) {
          if (!_args.get(i).equals(_args.get(j))) return false;
        }
      }
      return true;
    }
  }

  /** If this term is x(s1,...,sn) and extra = [t1,...,tm], this returns x(s1,...,sn,t1,...,tm). */
  public Term apply(List<Term> extra) {
    List<Term> newargs = new ArrayList<Term>(_args);
    newargs.addAll(extra);
    return new VarTerm(_x, newargs);
  }

  /**
   * This function applies gamma recursively on the arguments and the head and returns the
   * application of the substituted head to the substituted arguments.
   */
  public Term substitute(Substitution gamma) {
    List<Term> newargs = substituteArgs(gamma);
    if (gamma.get(_x) == null) return reconstruct(newargs);
    else return gamma.get(_x).apply(newargs);
  }

  /**
   * This does matching in an APPLICATIVE way: x(sk,...,sn) is instantiated by head(t1,...,tn) if
   * ti instantiates si for k ≤ i ≤ n (with x mapped to f(t1,...,t{k-1}).
   * It does NOT match modulo beta.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("VarTerm", "match", "argument term (other)");
    if (_args.size() == 0) return _x.match(other, gamma);
    if (!other.isFunctionalTerm() && !other.isVarTerm()) {
      throw new UnexpectedPatternError("VarTerm", "match", other.toString(),
                                       "a term x(s1,...,sn) or f(s1,...,sn)");
    }
    if (other.numberImmediateSubterms() < _args.size()) {
      return other.toString() + " does not instantiate " + toString() + " (too few arguments).";
    }
    int i = other.numberImmediateSubterms();
    int j = numberImmediateSubterms();
    for (; j > 0; i--, j--) {
      Term mysub = queryImmediateSubterm(j);
      Term hissub = other.queryImmediateSubterm(i);
      String warning = mysub.match(hissub, gamma);
      if (warning != null) return warning;
    }
    return _x.match(other.queryImmediateHeadSubterm(i), gamma);
  }

  /** This method gives a string representation of the term. */
  public String toString(VariableNamer namer) {
    String ret = _x.toString(namer);
    if (_args.size() > 0) {
      ret += "(" + _args.get(0).toString(namer);
      for (int i = 1; i < _args.size(); i++) ret += ", " + _args.get(i).toString(namer);
      ret += ")";
    }
    return ret;
  }

  /** This method verifies equality to another Term. */
  public boolean equals(Term term) {
    if (term == null) return false;
    if (!term.isVarTerm()) return false;
    if (!_x.equals(term.queryVariable())) return false;
    if (_args.size() != term.numberImmediateSubterms()) return false;
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).equals(term.queryImmediateSubterm(i+1))) return false;
    }
    return true;
  }
}

