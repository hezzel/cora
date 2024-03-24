/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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
import charlie.exceptions.InappropriatePatternDataError;
import charlie.types.Type;

/** A Constant that happens to be a Calculation Symbol. */
public class CalculationConstant extends LeafTermInherit implements CalculationSymbol {
  private Kind _kind;
  private Associativity _assoc;
  private int _priority;
  private String _name;

  CalculationConstant(String name, Type mytype, Kind mykind, Associativity assoc,
                      int infixPriority) {
    super(mytype);
    _name = name;
    _kind = mykind;
    _assoc = assoc;
    _priority = infixPriority;
    setVariables(ReplaceableList.EMPTY);
  }

  /** @return the kind of calculation symbol this is. */
  public Kind queryKind() { return _kind; }

  /** @return the associativity of the current symbol. */
  public Associativity queryAssociativity() { return _assoc; }

  /** @return the infix priority of the current symbol (or whatever if it is not infix). */
  public int queryInfixPriority() { return _priority; }

  /** @return the name of the current symbol. */
  public String queryName() { return _name; }

  /** @return a unique name for the current symbol. */
  public String toUniqueString() { return _name + "{" + queryType().toString() + "}#calc"; }

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
  public boolean isFirstOrder() { return false; }

  /** @return this */
  public FunctionSymbol queryRoot() { return this; }

  /** @return the arity of the type */
  public int queryArity() { return queryType().queryArity(); }

  /** @return this */
  public CalculationSymbol toCalculationSymbol() { return this; }

  /** Throws an error, because a calculation symbol is not a variable (or associated with one). */
  public Variable queryVariable() {
    throw new InappropriatePatternDataError("CalculationConstant" + _name, "queryVariable",
                                            "variables or lambda-expressions");
  }

  /**
   * Throws an error, because a calculation symbol is not a meta-application (or associated with
   * one).
   */
  public MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataError("CalculationConstant" + _name, "queryMetaVariable",
                                            "meta-variable applications (or terms headed by one)");
  }

  /** Returns the current value unmodified (there is nothing to substitute in a function symbol). */
  public Term substitute(Substitution gamma) {
    return this;
  }

  /**
   * This method checks that other is the same calculation symbol. If so, null is returned,
   * otherwise a description of the instantiation failure.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullPointerException("Other term in CalculationConstant::match");
    if (equals(other)) return null;
    return "calculation symbol " + _name + " is not instantiated by " + other.toString() + ".";
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
    return _name.equals(other.queryName());
  }
}

