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

package cora.immutabledata.terms;

import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.IndexingError;
import cora.exceptions.NullCallError;
import cora.exceptions.NullInitialisationError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;

/**
 * Variables are both used as parts of constraints, as binders in an abstraction, as generic
 * expression in terms and as open spots for matching in rules; this class represents all those
 * kinds of variables.
 * Variables can be renamed (both for reasons of α-conversion and renaming copies of rules), so
 * they are not defined by their name (although they must have one for printing purposes).
 */
public class Var implements Variable {
  private static int COUNTER = 0;
  private String _name;
  private Type _type;
  private int _index;

  /** Create a variable with the given name and type. */
  public Var(String name, Type type) {
    _name = name;
    _type = type;
    _index = COUNTER;
    COUNTER++;
    if (name == null) throw new NullInitialisationError("Var", "name");
    if (type == null) throw new NullInitialisationError("Var", "type");
  }

  /** @return VARTERM */
  public TermKind queryTermKind() {
    return Term.TermKind.VARTERM;
  }

  /** Returns the name this variable was set up with, or renamed to. */
  public String queryName() {
    return _name;
  }

  /** @return the type of the variable */
  public Type queryType() {
    return _type;
  }

  /** @return an integer uniquely identifying this variable */
  public int queryVariableIndex() {
    return _index;
  }

  /** @return the name of the variable, along with its index. */
  public String toString() {
    return _name;
  }

  /** @return this */
  public Variable queryVariable() {
    return this;
  }

  /** @throws InappropriatePatternDataError, as a variable does not have a function symbol root */
  public FunctionSymbol queryRoot() {
    throw new InappropriatePatternDataError("Var", "queryRoot", "functional terms");
  }

  /** @return 0, as a variable does not have subterms */
  public int numberImmediateSubterms() {
    return 0;
  }

  /** @throws IndexingError, as a variable does not have subterms */
  public Term queryImmediateSubterm(int i) {
    throw new IndexingError("Var", "queryImmediateSubterm", i);
  }

  /**
   * As we do not have a copy constructor, and do not consider variables equal if they share the
   * same name, two variables are considered equal only if they are the exact same object.
   * This also guarantees that renamings carry over to all instances of the renamed variable.
   */
  public boolean equals(Variable other) {
    return this == other;
  }

  /** A Variable can only be equal to another term if that term is this same Variable */
  public boolean equals(Term other) {
    if (other.queryTermKind() != Term.TermKind.VARTERM) return false;
    return equals(other.queryVariable());
  }
}

