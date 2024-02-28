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

import java.util.Map;
import java.util.Set;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullCallError;
import cora.types.Type;

/** An inheritable for all calculation symbols. */
public abstract class CalculationInherit extends LeafTermInherit implements CalculationSymbol {
  protected CalculationInherit(Type mytype) {
    super(mytype);
    setVariables(ReplaceableList.EMPTY);
  }

  /** @return true, since calculation symbols are guaranteed to be theory symbols. */
  public boolean isTheorySymbol() { return true; }

  /** @return true, since calculation symbols are theory terms */
  public boolean isTheoryTerm() { return true; }

  /** @return false */
  public boolean isValue() { return false; }

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
  public CalculationSymbol toCalculationSymbol() { return this; }

  /** Throws an error, because a calculation symbol is not a variable (or associated with one). */
  public Variable queryVariable() {
    throw new InappropriatePatternDataError("CalculationInherit", "queryVariable",
                                            "variables or lambda-expressions");
  }

  /**
   * Throws an error, because a calculation symbol is not a meta-application (or associated with
   * one).
   */
  public MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataError("CalculationInherit", "queryMetaVariable",
                                            "meta-variable applications (or terms headed by one)");
  }

  /** Returns the current value unmodified (there is nothing to substitute in a value). */
  public Term substitute(Substitution gamma) {
    return this;
  }

  /**
   * This method checks that other is the same calculation symbol. If so, null is returned,
   * otherwise a description of the instantiation failure.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("CalculationInherit", "match", "other term");
    if (equals(other)) return null;
    return "calculation symbol " + toString() + " is not instantiated by " + other.toString() + ".";
  }

  /** f =_α^{μ,ξ,k} t if and only if f and t are the same value. */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isConstant()) return false;
    return equals(term.queryRoot());
  }

  /** We are only equal to other calculation symbols of the same name and type. */
  public boolean equals(FunctionSymbol other) {
    if (other == null) return false;
    if (!other.isTheorySymbol()) return false;
    if (!queryType().equals(other.queryType())) return false;
    return queryName().equals(other.queryName());
  }
}

