/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import java.util.Map;
import charlie.types.Base;
import charlie.types.TypeFactory;

/**
 * Values are constants of a theory sorts that cannot be rewritten; they are the representations of
 * the elements of the underlying sets.
 */
public abstract class ValueInherit extends LeafTermInherit implements Value {
  protected ValueInherit(Base mysort) {
    super(mysort);
    setVariables(ReplaceableList.EMPTY);
  }

  /** The type of a Value is always one of the theory sorts. */
  public Base queryType() { return (Base)super.queryType(); }

  /** @return 0, since values cannot be applied. */
  public int queryArity() { return 0; }

  /** @return true, since values are guaranteed to be theory symbols. */
  public boolean isTheorySymbol() { return true; }

  /** @return true, since values are theory terms */
  public boolean isTheoryTerm() { return true; }

  /** @return true */
  public boolean isValue() { return true; }

  /** @return true */
  public boolean isConstant() { return true; }

  /** @return true */
  public boolean isFunctionalTerm() { return true; }

  /** @return true */
  public boolean isApplicative() { return true; }

  /** @return true */
  public boolean isFirstOrder() { return true; }

  /** @return this */
  public FunctionSymbol queryRoot() { return this; }

  /** @return this */
  public Value toValue() { return this; }

  /** @return null, since a value is not a calculation symbol */
  public CalculationSymbol toCalculationSymbol() { return null; }

  public boolean isIntegerValue() { return queryType().equals(TypeFactory.intSort); }

  public boolean isBooleanValue() { return queryType().equals(TypeFactory.boolSort); }

  public boolean isStringValue() { return queryType().equals(TypeFactory.stringSort); }

  /** Throws an error, because a value is not a variable (or associated with one). */
  public Variable queryVariable() {
    throw new InappropriatePatternDataException("ValueInherit", "queryVariable",
                                                "variables or lambda-expressions");
  }

  /** Throws an error, because a value is not a meta-application (or associated with one). */
  public MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataException("ValueInherit", "queryMetaVariable",
                              "meta-variable applications (or terms headed by one)");
  }

  /** Returns the current value unmodified (there is nothing to substitute in a value). */
  public Term substitute(Substitution gamma) {
    return this;
  }

  /**
   * This method checks that other is the same value. If so, null is returned, otherwise a
   * description of the instantiation failure.
   */
  public String match(Term other, Substitution gamma) {
    if (equals(other)) return null;
    return "value " + toString() + " is not instantiated by " + other.toString() + ".";
  }

  /** f =_α^{μ,ξ,k} t if and only if f and t are the same value. */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isValue()) return false;
    return equals(term.queryRoot());
  }
}

