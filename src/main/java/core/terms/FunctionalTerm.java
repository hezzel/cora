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

package cora.core.terms;

import java.util.ArrayList;
import cora.exceptions.ArityError;
import cora.exceptions.IndexingError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.NullCallError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Substitution;

/**
 * FunctionalTerms are terms of the form f(s1,...,sn) where s1,...,sn are all terms and f is a
 * function symbol.
 * Here, n may be 0, but both n and the types of s1,...,sn are restricted by the type of f. 
 * Application of functions must take typing into account.
 */
public class FunctionalTerm implements Term {
  private FunctionSymbol _f;
  private ArrayList<Term> _args;
  private Type _outputType;

  /**
   * This constructor is used to create a constant term (which may, however, still have higher
   * type). Throws an error if constant is null.
   */
  public FunctionalTerm(FunctionSymbol constant) {
    if (constant == null) throw new NullInitialisationError("FunctionalTerm", "constant");
    _f = constant;
    _args = new ArrayList<Term>();
    _outputType = constant.queryType();
  }

  /**
   * This helper function handles the functionality of all constructors.
   * The given function symbol and argument list become the property of this functional term, and
   * the output type is derived from the two given arguments.
   * If there are any problems -- such as f or an argument being null, or the types not checking
   * out -- an appropriate Error is thrown. However, it *is* assumed that args is not null.
   */
  private void construct(FunctionSymbol f, ArrayList<Term> args) {
    if (f == null) throw new NullInitialisationError("FunctionalTerm", "function symbol");
    Type type = f.queryType();
    for (int i = 0; i < args.size(); i++) {
      Term arg = args.get(i);
      if (arg == null) {
        throw new NullInitialisationError("FunctionalTerm", "passing a null argument to " +
          f.toString() + ".");
      }
      if (type.queryTypeKind() != Type.TypeKind.ARROWTYPE) {
        throw new ArityError("FunctionalTerm", "constructor", "symbol " + f.toString() +
          " has maximum arity " + i + " and is given " + args.size() + " arguments.");
      }
      Type input = type.queryArrowInputType();
      if (!input.equals(arg.queryType())) {
        throw new TypingError("FunctionalTerm", "constructor", "arg " + i + " of " +
          f.toString(), arg.queryType() == null ? "null" : arg.queryType().toString(),
          input.toString());
      }
      type = type.queryArrowOutputType();
    }
    _f = f;
    _args = args;
    _outputType = type;
  }

  /**
   * This constructor is used to create a term which takes one argument.
   * Throws an error if the constant is null or does not have arity 1, or the argument is null.
   */
  public FunctionalTerm(FunctionSymbol f, Term arg) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(arg);
    construct(f, args);
  }

  /**
   * This constructor is used to create a term which takes two arguments.
   * Throws an error if the constant does not have arity 2, or one of the arguments is null.
   */
  public FunctionalTerm(FunctionSymbol f, Term arg1, Term arg2) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(arg1);
    args.add(arg2);
    construct(f, args);
  }

  /**
   * This constructor is used to create a term f(s1,...,sn) with n >= 0.
   * Throws an error if n does not match the arity of f, or if the types of the arguments are not
   * the expected input types of f.
   */
  public FunctionalTerm(FunctionSymbol f, ArrayList<Term> args) {
    if (args == null) throw new NullInitialisationError("FunctionalTerm", "argument list");
    construct(f, new ArrayList<Term>(args));
  }

  /**
   * This constructor is used to create a term f(s1,...,sn) with n >= 0 and the given output type,
   * without any checks of for instance type correctness being done.
   * Moreover, the array list args becomes the property of the new term, and may not be modified
   * afterwards.
   * Only for features like substitution or simplifications. Be very careful using this!
   */
  private FunctionalTerm(ArrayList<Term> args, FunctionSymbol f, Type outputType) {
    _f = f;
    _args = args;
    _outputType = outputType;
  }

  /** @return FUNCTIONALTERM */
  public TermKind queryTermKind() {
    return TermKind.FUNCTIONALTERM;
  }

  /** For a term f(s1,...,sn), this returns n. */
  public int numberImmediateSubterms() {
    return _args.size();
  }

  /** For a term f(s1,...,sn), this returns si if 1 <= i <= n, and throws an error otherwise. */
  public Term queryImmediateSubterm(int i) {
    if (i <= 0 || i > _args.size()) {
      throw new IndexingError("FunctionalTerm", "queryImmediateSubterm", i, 1, _args.size());
    }
    return _args.get(i-1);
  }

  /** For a term f(s1,...,sn), this returns f. */
  public FunctionSymbol queryRoot() {
    return _f;
  }

  /** Throws an error, because a functional term is not a variale. */
  public Variable queryVariable() {
    throw new InappropriatePatternDataError("FunctionalTerm", "queryVariable",
                                            "variables or lambda-expressions");
  }

  /** This method returns the output type of the term. */
  public Type queryType() {
    return _outputType;
  }

  /** 
   * This method applies the substitution recursively to the arguments and returns the term that
   * results from replacing our old arguments by these substituted ones.
   */
  public Term substitute(Substitution gamma) {
    ArrayList<Term> args = new ArrayList<Term>(_args);
    for (int i = 0; i < args.size(); i++) {
      Term t = args.get(i).substitute(gamma);
      if (t == null) {
        throw new Error("Substituting " + args.get(i).toString() + " results in null!");
      }   
      args.set(i, t); 
    }
    return new FunctionalTerm(args, _f, _outputType);
  }

  /** 
   * This method checks that other has the same root symbol as we do, and if so, that all the
   * parameters match (updating the substitution as we go along).
   * If everything matches, null is returned; otherwise a description of the instantiation failure.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("FunctionalTerm", "match", "argument term (other)");
    if (other.queryTermKind() != TermKind.FUNCTIONALTERM ||
        !_f.equals(other.queryRoot()) || _args.size() != other.numberImmediateSubterms()) {
      return "functional term " + toString() + " is not instantiated by " + other.toString() + ".";
    }   
    for (int i = 0; i < _args.size(); i++) {
      String warning = _args.get(i).match(other.queryImmediateSubterm(i+1), gamma);
      if (warning != null) return warning;
    }
    return null;
  }

  /** This method gives a string representation of the term. */
  public String toString() {
    String ret = _f.toString();
    if (_args.size() > 0) {
      ret += "(" + _args.get(0).toString();
      for (int i = 1; i < _args.size(); i++) ret += ", " + _args.get(i).toString();
      ret += ")";
    }
    return ret;
  }

  /** This method verifies equality to another Term. */
  public boolean equals(Term term) {
    if (term == null) return false;
    if (term.queryTermKind() != TermKind.FUNCTIONALTERM) return false;
    if (!_f.equals(term.queryRoot())) return false;
    if (_args.size() != term.numberImmediateSubterms()) return false;
    for (int i = 0; i < _args.size(); i++) {
      if (!_args.get(i).equals(term.queryImmediateSubterm(i+1))) return false;
    }
    return true;
  }
}

