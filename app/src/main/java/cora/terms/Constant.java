/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

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

import java.util.Map;
import java.util.Set;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.NullCallError;
import cora.types.Type;

/**
 * Constants are the default kind of FunctionSymbol.
 * They are called Constants because they can also be seen as constant terms.
 */
class Constant extends LeafTermInherit implements FunctionSymbol {
  private final String _name;

  /**
   * A constant is always identified by the combination of its name and its type.
   * Throws an error if the name or type is null, or if name is the empty string.
   */
  Constant(String name, Type type) {
    super(type);
    _name = name;
    if (name == null) throw new NullInitialisationError("Constant", "name");
    if (name.equals("")) throw new Error("Function Symbol created with empty name.");
    setVariables(ReplaceableList.EMPTY);
  }

  /** Returns the name of the current user-defined symbol. */
  public String queryName() {
    return _name;
  }

  /** Add a description of the current function symbol to the string; the type is not indicated. */
  public void addToString(StringBuilder builder, Map<Replaceable,String> renaming,
                          Set<String> avoid) {
    builder.append(_name);
  }

  /** Returns the number of terms this constant may (at most) be applied to. */
  public int queryArity() {
    return queryType().queryArity();
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
    if (symbol.isTheorySymbol()) return false;
    return queryType().equals(symbol.queryType());
  }

  /** @return false */
  public boolean isVariable() { return false; }

  /** @return false */
  public boolean isVarTerm() { return false; }

  /** @return true */
  public boolean isConstant() { return true; }

  /** @return true */
  public boolean isFunctionalTerm() { return true; }

  /** @return false */
  public boolean isMetaApplication() { return false; }

  /** @return true */
  public boolean isApplicative() { return true; }

  /** @return true if the type of the constant is a base type */
  public boolean isFirstOrder() {
    return queryType().isBaseType();
  }

  /** @return false, since theory symbols use a different class */
  public boolean isTheorySymbol() {
    return false;
  }

  /** @return false, since this is not a theory symbol */
  public boolean isTheoryTerm() {
    return false;
  }

  /** @return false, since values use a different class */
  public boolean isValue() {
    return false;
  }

  /** @return null, since this is not a value */
  public Value toValue() {
    return null;
  }

  /** @return null, since this is not a calculation symbol */
  public CalculationSymbol toCalculationSymbol() {
    return null;
  }

  /** Returns the current symbol f, which is the root of the corresponding term f(). */
  public FunctionSymbol queryRoot() {
    return this;
  }

  /** Throws an error, because a constant is not a variale (or associated with one). */
  public Variable queryVariable() {
    throw new InappropriatePatternDataError("Constant", "queryVariable",
                                            "variables or lambda-expressions");
  }

  /** Throws an error, because a constant is not a meta-application (or associated with one). */
  public MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataError("Constant", "queryMetaVariable",
                                            "meta-variable applications (or terms headed by one)");
  }

  /** Returns the current constant unmodified (there is nothing to substitute in a constant). */
  public Term substitute(Substitution gamma) {
    return this;
  }

  /**
   * This method checks that other is the same constant. If so, null is returned, otherwise a
   * description of the instantiation failure.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("Constant", "match", "other term");
    if (equals(other)) return null;
    return "constant " + _name + " is not instantiated by " + other.toString() + ".";
  }

  /** f =_α^{μ,ξ,k} t if and only if f and t are the same constant. */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isConstant()) return false;
    return equals(term.queryRoot());
  }
}
