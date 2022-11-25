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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.IndexingError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.IllegalTermError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.ArrowType;

/** Abstractions are terms of the form λx.s where x is a variable and s a term. */
public class Abstraction extends TermInherit implements Term {
  private Variable _binder;
  private Term _subterm;
  private Type _type;

  /**
   * Generates the abstraction λ<binder>.<subterm>.
   * Throws an IllegalTermError if the given binder is not marked as a binder variable.
   */
  public Abstraction(Variable binder, Term subterm) {
    if (binder == null) throw new NullInitialisationError("Abstraction", "binder");
    if (subterm == null) throw new NullInitialisationError("Abstraction", "subterm");
    _binder = binder;
    _subterm = subterm;
    _type = new ArrowType(binder.queryType(), subterm.queryType());
    if (!_binder.isBinderVariable()) {
      throw new IllegalTermError("Creating an abstraction λ" + binder.toString() + "." +
        subterm.toString() + " with a variable that is not marked as a binder var!");
    }
    initiateVars();
  }

  /** @return σ → τ for an abstraction λx:σ.t with t : τ */
  public Type queryType() {
    return _type;
  }

  /** @return false */
  public boolean isVariable() {
    return false;
  }

  /** @return false */
  public boolean isConstant() {
    return false;
  }

  /** @return false */
  public boolean isFunctionalTerm() {
    return false;
  }

  /** @return false */
  public boolean isVarTerm() {
    return false;
  }

  /** @return true */
  public boolean isAbstraction() {
    return true;
  }

  /** @return 1 */
  public int numberImmediateSubterms() {
    return 1;
  }

  /** @return the immediate subterm if i = 1; otherwise throws an IndexingError. */
  public Term queryImmediateSubterm(int i) {
    if (i != 1) {
      throw new IndexingError("Abstraction", "queryImmediateSubterm", i, 1, 1);
    }
    return _subterm;
  }

  /** @return the current term if i = 1; otherwise throws an IndexingError. */
  public Term queryImmediateHeadSubterm(int i) {
    if (i != 1) {
      throw new IndexingError("Abstraction", "queryImmediateHeadSubterm", i, 1, 1);
    }
    return this;
  }

  /** Throws an error, because an abstraction does not have a root. */
  public FunctionSymbol queryRoot() {
    throw new InappropriatePatternDataError("Abstraction", "queryRoot", "functional terms");
  }

  /** @return the bound variable for this abstraction. */
  public Variable queryVariable() {
    return _binder;
  }

  /** @return false, since an abstraction cannot be a part of a first-order term. */
  public boolean isFirstOrder() {
    return false;
  }

  /** @return false, since an abstraction is not an applicative term. */
  public boolean isApplicative() {
    return false;
  }

  /** @return whether the immediate argument is a pattern. */
  public boolean isPattern() {
    return _subterm.isPattern();
  }

  /**
   * Replaces the subterm at the given position and returns the result (without affecting the
   * current term).
   * Unlike substitution, this does not cause the binder of the abstraction to be changed;
   * variables in the replacement might be captured due to this.
   */
  public Term replaceSubterm(Position pos, Term replacement) {
    if (pos.isEmpty()) {
      if (!_type.equals(replacement.queryType())) {
        throw new TypingError("Abstraction", "replaceSubterm", "replacement term " + 
                    replacement.toString(), replacement.queryType().toString(),
                    _type.toString());
      }
      return replacement;
    }

    Term newsub = _subterm.replaceSubterm(pos.queryTail(), replacement);
    return new Abstraction(_binder, newsub);
  }

  /** For λx.s, this returns the pair (free variables of s \ {x}, bound variables of s ∪ {x}. */
  public EnvironmentPair allVars() {
    EnvironmentPair child = new EnvironmentPair(_subterm.freeVars(), _subterm.boundVars());
    return child.markFreeVarAsBound(_binder);
  }

  /**
   * For extra = [], this returns the current term; for extra = [s1;...;sn] and the current term
   * λx.t, this returns t[x:=s1].apply([s2;...;sn]).
   */
  public Term apply(List<Term> extra) {
    if (extra.size() == 0) return this;
    
    Term s = this;
    Substitution gamma = new Subst();
    int i = 0;
    
    for (; i < extra.size() && s.isAbstraction(); i++) {
      Variable x = s.queryVariable();
      gamma.replace(x, extra.get(i));
      s = s.queryImmediateSubterm(1);
    }

    Term t = s.substitute(gamma);
    return t.apply(extra.subList(i, extra.size()));
  }

  /** Applies the given substitution recursively on the term and returns the result. */
  public Term substitute(Substitution gamma) {
    Variable freshvar = new BinderVariable(_binder.queryName(), _binder.queryType());
    Term subtermSubstitute;
    if (gamma.extend(_binder, freshvar)) {
      subtermSubstitute = _subterm.substitute(gamma);
      gamma.delete(_binder);
    }   
    else {
      Term previous = gamma.get(_binder);
      gamma.replace(_binder, freshvar);
      subtermSubstitute = _subterm.substitute(gamma);
      gamma.replace(_binder, previous);
    }   
    return new Abstraction(freshvar, subtermSubstitute);
  }

  /**
   * This function implements plain matching: gamma is updated so that <this> gamma = other, where
   * variables at the head of a non-trivial var term may not be instantiated by abstractions.
   * If there is no suitable update for gamma, a string is returned explaining why not.
   */
  public String plainMatch(Term other, Substitution gamma) {
    return null; /* TODO */
  }

  /** Returns a string representation of the current term. */
  public String toString(VariableNamer namer) {
    String binder = _binder.toString(namer);
    return "λ" + binder + "." + _subterm.toString(namer);
  }

  /** Determines whether the current term is alpha-equal to the given term. */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isAbstraction()) return false;
    Variable x = _binder;
    Variable y = term.queryVariable();
    if (!x.queryType().equals(y.queryType())) return false;
    if (mu.containsKey(x)) {
      throw new IllegalTermError("Calling alphaEquals when mu already maps " + x.toString() + ".");
    }
    if (xi.containsKey(y)) {
      throw new IllegalTermError("Calling alphaEquals when xi already maps " + y.toString() + ".");
    }
    mu.put(x, k);
    xi.put(y, k);
    boolean retval = _subterm.alphaEquals(term.queryImmediateSubterm(1), mu, xi, k + 1);
    mu.remove(x);
    xi.remove(y);
    return retval;
  }
}

