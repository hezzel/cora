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

import java.lang.Iterable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.Set;
import java.util.TreeSet;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.IndexingError;
import cora.exceptions.IllegalTermError;
import cora.exceptions.NullInitialisationError;
import cora.types.Type;
import cora.types.TypeFactory;

/** Abstractions are terms of the form λx.s where x is a variable and s a term. */
class Abstraction extends TermInherit {
  private Variable _binder;
  private Term _subterm;
  private Type _type;

  /**
   * Generates the abstraction λ<binder>.<subterm>.
   * Throws an IllegalArgumentError if the given binder is not marked as a binder variable.
   */
  public Abstraction(Variable binder, Term subterm) {
    if (binder == null) throw new NullInitialisationError("Abstraction", "binder");
    if (subterm == null) throw new NullInitialisationError("Abstraction", "subterm");
    if (!binder.isBinderVariable()) {
      throw new IllegalTermError("Abstraction", binder.toString() + " is not marked as a binder.");
    }
    _binder = binder;
    _subterm = subterm;
    _type = TypeFactory.createArrow(binder.queryType(), subterm.queryType());
    VariableList frees = subterm.vars().remove(binder);
    VariableList bounds = subterm.boundVars().add(binder);
    setVariables(frees, bounds);
    // TODO: make sure the term is well-behaved by creating a fresh binder variable for any
    // instance of binder in subterm
  }

  /** @return <type of bindre> → <type of subterm> */
  public Type queryType() {
    return _type;
  }

  /** @return false, since an abstraction is not a variable */
  public boolean isVariable() {
    return false;
  }

  /** @return false, since an abstraction is not a constant */
  public boolean isConstant() {
    return false;
  }

  /** @return false, since an abstraction is not a functional term */
  public boolean isFunctionalTerm() {
    return false;
  }

  /** @return false, since an abstraction is not a varterm */
  public boolean isVarTerm() {
    return false;
  }

  /** @return false, since an abstraction is not an application */
  public boolean isApplication() {
    return false;
  }

  /** @return true, since this is indeed an abstraction */
  public boolean isAbstraction() {
    return true;
  }

  /** @return false, since an abstraction is not a beta-redex */
  public boolean isBetaRedex() {
    return false;
  }

  /** @return 0, since the subterm is not an argument */
  public int numberArguments() {
    return 0;
  }

  /** @return the empty list, since the subterm is not an argument */
  public ArrayList<Term> queryArguments() {
    return new ArrayList<Term>();
  }

  /** @throws IndexingError, since the subterm is not an argument */
  public Term queryArgument(int i) {
    throw new IndexingError("Abstraction", "queryArgument", i);
  }

  /** Either returns this (if i == 0) or throws an IndexingError. */
  public Term queryImmediateHeadSubterm(int i) {
    if (i == 0) return this;
    throw new IndexingError("Abstraction", "queryImmediateHeadSubterm", i);
  }

  /** @return this, since this is not an application */
  public Term queryHead() {
    return this;
  }

  /**
   * @throws InappropriatePatternDataError, as an abstraction does not have a function symbol root
   */
  public FunctionSymbol queryRoot() {
    throw new InappropriatePatternDataError("Var", "queryRoot", "functional terms");
  }

  /** @return the binder of the abstraction */
  public Variable queryVariable() {
    return _binder;
  }

  /** @return false, since an abstraction is not first-ordre */
  public boolean isFirstOrder() {
    return false;
  }

  /** @return whether this abstraction is a pattern (if and only if the immediate subterm is) */
  public boolean isPattern() {
    return _subterm.isPattern();
  }

  public List<Path> queryPositions() {
    // TODO
    return null;
  }

  public Term querySubterm(Position pos) {
    // TODO
    return null;
  }

  public Term querySubterm(HeadPosition pos) {
    // TODO
    return null;
  }

  public Term replaceSubterm(Position pos, Term replacement) {
    // TODO
    return null;
  }

  public Term replaceSubterm(HeadPosition pos, Term replacement) {
    // TODO
    return null;
  }

  public Term substitute(Substitution gamma) {
    // TODO
    return null;
  }

  public String match(Term other, Substitution gamma) {
    // TODO
    return null;
  }

  /**
   * Appends a string representation of the current abstraction to the given string builder.
   * The binder is renamed if its default name occurs in avoid.
   */
  public void addToString(StringBuilder builder, Map<Variable,String> renaming, Set<String> avoid) {
    String bname = _binder.queryName();
    String name = bname;
    for (int i = 1; avoid.contains(name); i++) name = bname + i;
    renaming.put(_binder, name);
    avoid.add(name);

    builder.append("λ");
    builder.append(renaming.get(_binder));
    builder.append(".");
    _subterm.addToString(builder, renaming, avoid);

    avoid.remove(name);
    renaming.remove(_binder);
    // note that it is not possible that renaming[binder] was previously set, as this would violate
    // the well-definedness constraint; hence, we do not have to restore anything here
  }

  public boolean equals(Term other) {
    // TODO
    return false;
  }
}

