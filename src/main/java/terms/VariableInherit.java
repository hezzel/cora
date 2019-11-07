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
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullCallError;
import cora.exceptions.NullInitialisationError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.Sort;

/**
 * Variables are both used as parts of constraints, as binders in an abstraction, as generic
 * expressions in terms and as open spots for matching in rules; this class represents all those
 * kinds of variables.
 *
 * Variables have a name for printing purposes, but are not uniquely defined by it (distinct
 * variables may have the same name and type, although this will typically be avoided within a
 * single term).  Rather, variables are uniquely identified by an internally kept index.
 *
 * Variables can be marked as occurring in Vfree (the set of "free" variables; these may be used
 * for matching) or Vbound (the set of "bound" variables; these may become free in some contexts
 * but may never be used for matching non-variables).
 *
 * This class is used to define shared functionality for all kinds of Variables; inheriting
 * classes define additional information for instance for both free and bound variables.
 */
abstract class VariableInherit extends LeafTermInherit implements Variable {
  protected static int COUNTER = 0;
  private String _name;
  private int _index;

  public abstract String match(Term other, Substitution gamma);

  /** Helper function to return the current classname for use in Errors. */
  private String queryMyClassName() {
    return "VariableInherit (" + this.getClass().getSimpleName() + ")";
  }

  /** Create a variable with the given name and type. */
  public VariableInherit(String name, Type type) {
    super(type);
    _name = name;
    _index = COUNTER;
    COUNTER++;
    if (name == null) throw new NullInitialisationError(queryMyClassName(), "name");
  }

  /** @return true */
  public boolean isVariable() { return true; }

  /** @return true */
  public boolean isVarTerm() { return true; }

  /** @return false */
  public boolean isConstant() { return false; }

  /** @return false */
  public boolean isFunctionalTerm() { return false; }

  /** Returns the name this variable was set up with. */
  public String queryName() {
    return _name;
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
    throw new InappropriatePatternDataError(queryMyClassName(), "queryRoot", "functional terms");
  }

  /** Adds the current variable into env. */
  public void updateVars(Environment env) {
    env.add(this);
  }

  /** Returns the VarTerm x(args). */
  public Term apply(List<Term> args) {
    return new VarTerm(this, args);
  }

  /** @return gamma(x) if the current variable is x and x in dom(gamma), otherwise just x */
  public Term substitute(Substitution gamma) {
    if (gamma == null) {
      throw new NullCallError(queryMyClassName(), "substitute", "substitution gamma");
    }
    return gamma.getReplacement(this);
  }

  /**
   * Two variables are equal if and only if they share an index and have the same type.
   * Currently, this can only occur if they are the same object, but this may change in the future.
   */
  public boolean equals(Variable other) {
    return other.queryVariableIndex() == _index && queryType().equals(other.queryType());
  }

  /** A Variable can only be equal to another term if that term is this same Variable */
  public boolean equals(Term other) {
    if (!other.isVariable()) return false;
    return equals(other.queryVariable());
  }

  /** Implements a total ordering on variables using the index. */
  public int compareTo(Variable other) {
    if (_index < other.queryVariableIndex()) return -1;
    if (_index > other.queryVariableIndex()) return 1;
    return 0;
  }
}

