/**************************************************************************************************
 Copyright 2026 Cynthia Kop

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
import java.util.Set;
import charlie.types.Type;
import charlie.types.TVarSet;
import charlie.terms.replaceable.ReplaceableSet;

/**
 * An inheritable that can be used by all kinds of function symbol.  It handles most of the
 * default Term functionality, but allows inheriting classes to set the "special" value, infix
 * properties, and to define class-specific additional functionality.
 * */
public abstract class FunctionSymbolInherit extends LeafTermInherit implements FunctionSymbol {
  private final String _name;
  private final String _special;

  protected FunctionSymbolInherit(String name, Type type, String special) {
    super(type);
    setVariables(ReplaceableSet.EMPTY, TVarSet.of(type));
    _name = name;
    _special = special;
  }

  @Override
  public final String queryName() { return _name; }
  @Override
  public final String querySpecial() { return _special; }
  @Override
  public final int queryArity() { return queryType().queryArity(); }
  @Override
  public final boolean isConstant() { return true; }
  @Override
  public final boolean isFunctionalTerm() { return true; }
  @Override
  public final boolean isApplicative() { return true; }
  @Override
  public final FunctionSymbol queryRoot() { return this; }
  
  /** Throws an exception, because a function symbol is not a variable (or associated with one). */
  @Override
  public final Variable queryVariable() {
    throw new InappropriatePatternDataException("FunctionSymbolInherit", "queryVariable",
                                                "variables or lambda-expressions");
  }

  /**
   * Throws an exception, because a function symbol is not a meta-application (or associated with
   * one).
   */
  @Override
  public final MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataException("FunctionSymbolInherit", "queryMetaVariable",
                                      "meta-variable applications (or terms headed by one)");
  }

  /** @return true if the type of the constant is a level-0 type. */
  @Override
  public boolean isFirstOrder() {
    return queryType().isZeroSort();
  }

  /** Stores the present symbol into storage. */
  @Override
  public final void storeFunctionSymbols(Set<FunctionSymbol> storage) {
    storage.add(this);
  }

  @Override
  public final boolean equals(FunctionSymbol other) {
    return other != null &&
           other.queryName().equals(_name) &&
           other.querySpecial().equals(_special) &&
           other.queryType().equals(queryType());
  }

  @Override
  public final int compareTo(FunctionSymbol symbol) {
    int ret = _name.compareTo(symbol.queryName());
    if (ret != 0) return ret;
    ret = _special.compareTo(symbol.querySpecial());
    if (ret != 0) return ret;
    return queryType().compareTo(symbol.queryType());
  }

  /**
   * @return true if the symbol's type can be instantiated so that we become equal to other, and in
   * this case also updates the typeMapping accordingly.
   * When false is returned, there may still be some updates to the typeMapping!
   */
  @Override
  public final boolean match(FunctionSymbol other, Type.MSubstitution typeMapping) {
    if (other == null) return false;
    if (!_name.equals(other.queryName())) return false;
    if (!_special.equals(other.querySpecial())) return false;
    return queryType().match(other.queryType(), typeMapping);
  }

  /** There are no binders to rename in a function symbol, so this returns the symbol unmodified. */
  @Override
  public final FunctionSymbol renameAndRefreshBinders(Map<Variable,Variable> renaming) {
    return this;
  }

  /** f =_α^{μ,ξ,k} t if and only if f and t are the same constant. */
  @Override
  public final boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi,
                                   int k) {
    if (!term.isConstant()) return false;
    return equals(term.queryRoot());
  }

  /**
   * To support most practical uses of function symbols, we default to determining the hash code
   * simply by the name of the function symbol.
   */
  @Override
  public int hashCode(Map<Variable,Integer> mu) {
    return _name.hashCode();
  }
}
