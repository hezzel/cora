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
import cora.terms.positions.AbstractionPosition;
import cora.terms.positions.EmptyPosition;

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

  /** @return the immediate subterm if i = 0; otherwise throws an IndexingError. */
  public Term queryImmediateSubterm(int i) {
    if (i != 0) {
      throw new IndexingError("Abstraction", "queryImmediateSubterm", i, 1, 1);
    }
    return _subterm;
  }

  /** @return the current term if i = 0; otherwise throws an IndexingError. */
  public Term queryImmediateHeadSubterm(int i) {
    if (i != 0) {
      throw new IndexingError("Abstraction", "queryImmediateHeadSubterm", i, 0, 0);
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

  /** @return whether the immediate argument is a pattern. */
  public boolean isPattern() {
    return _subterm.isPattern();
  }

  /** @return the set of all positions = {ε} ∪ { 0 p | p ∈ Positions(subterm) } */
  public List<Position> queryAllPositions() {
    List<Position> ret = _subterm.queryAllPositions();
    for (int i = 0; i < ret.size(); i++) {
      ret.set(i, new AbstractionPosition(ret.get(i)));
    }
    ret.add(new EmptyPosition());
    return ret;
  }

  /** @return the subterm at the given position */
  public Term querySubterm(Position pos) {
    if (pos.isEmpty()) return this;
    return _subterm.querySubterm(pos.queryTail());
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

  /** For λx.s, this returns the free variables of s, excluding x (as x is bound in this term). */
  public Environment allVars() {
    return _subterm.freeVars().remove(_binder);
  }

  /**
   * For extra = [], this returns the current term; for extra = [s1;...;sn] and the current term
   * λx.t, this returns t[x:=s1].apply([s2;...;sn]).
   */
  public Term apply(List<Term> extra) {
    return null; /* TODO */
  }

  /** Applies the given substitution recursively on the term and returns the result. */
  public Term substitute(Substitution gamma) {
    return null; /* TODO */
  }

  /**
   * This function implements PLAIN matching: gamma is updated so that <this> gamma = other, where
   * variables at the head of a non-trivial var term may not be instantiated by abstractions.
   * If there is no suitable update for gamma, a string is returned explaining why not.
   */
  public String match(Term other, Substitution gamma) {
    return null; /* TODO */
  }

  /** Returns a string representation of the current term. */
  public String toString(VariableNamer namer) {
    return "λ" + _binder.toString(namer) + "." + _subterm.toString(namer);
  }

  /** Returns whether the current term is alpha-equal to the given other term. */
  public boolean equals(Term other) {
    if (!other.isAbstraction()) return false;
    /* TODO */
    if (!_binder.equals(other.queryVariable())) return false;
    return _subterm.equals(other.queryImmediateSubterm(0));
  }
}

