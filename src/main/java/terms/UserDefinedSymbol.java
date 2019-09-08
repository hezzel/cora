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
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.NullCallError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;

/**
 * UserDefinedSymbols are FunctionSymbols which are not predefined within Cora.
 * They can be seen as constant terms.
 */
public class UserDefinedSymbol extends LeafTermInherit implements FunctionSymbol {
  private String _name;

  /**
   * A user-defined symbol is always identified by the combination of its name and its type.
   * Throws an error if the name or type is null, or if name is the empty string.
   */
  public UserDefinedSymbol(String name, Type type) {
    super(type);
    _name = name;
    if (name == null) throw new NullInitialisationError("UserDefinedSymbol", "name");
    if (name.equals("")) throw new Error("Function Symbol created with empty name.");
  }

  /** Returns the name of the current user-defined symbol. */
  public String queryName() {
    return _name;
  }

  /** Returns a string that describes the function symbol; the type is not indicated. */
  public String toString() {
    return _name;
  }

  /**
   * Returns a string that uniquely identifies the function symbol (by combining its name and
   * type).
   */
  public String toUniqueString() {
    return _name + "{" + queryType().toString() + "}";
  }

  public boolean equals(FunctionSymbol symbol) {
    if (symbol == null) return false;
    if (!_name.equals(symbol.queryName())) return false;
    return queryType().equals(symbol.queryType());
  }

  /** @return FUNCTIONALTERM */
  public TermKind queryTermKind() {
    return TermKind.FUNCTIONALTERM;
  }

  /** Returns the current symbol f, which is the root of the corresponding term f(). */
  public FunctionSymbol queryRoot() {
    return this;
  }

  /** Throws an error, because a constant is not a variale (or associated with one). */
  public Variable queryVariable() {
    throw new InappropriatePatternDataError("UserDefinedSymbol", "queryVariable",
                                            "variables or lambda-expressions");
  }

  /** Does nothing, since a function symbol does not use any variables. */
  public void updateVars(Environment env) {}

  /** Returns the current constant unmodified (there is nothing to substitute in a constant). */
  public Term substitute(Substitution gamma) {
    return this;
  }

  /**
   * This method checks that other is the same constant. If so, null is returned, otherwise a
   * description of the instantiation failure.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("UserDefinedSymbol", "match", "other term");
    if (equals(other)) return null;
    return "constant " + _name + " is not instantiated by " + other.toString() + ".";
  }

  public boolean equals(Term term) {
    if (term == null) return false;
    if (term.queryTermKind() != TermKind.FUNCTIONALTERM) return false;
    if (term.numberImmediateSubterms() != 0) return false;
    return equals(term.queryRoot());
  }
}

