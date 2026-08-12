/**************************************************************************************************
 Copyright 2024--2026 Cynthia Kop

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
import charlie.types.Type;
import charlie.types.TVar;
import charlie.types.TVarSet;
import charlie.terms.replaceable.ReplaceableSet;

/** A Constant that happens to be a Calculation Symbol. */
public class CalculationConstant extends FunctionSymbolInherit implements CalculationSymbol {
  private Kind _kind;
  private Associativity _assoc;
  private int _priority;
  private String _name;

  CalculationConstant(String name, Type mytype, Kind mykind, Associativity assoc,
                      int infixPriority) {
    super(name, mytype, "calc");
    _name = name;
    _kind = mykind;
    _assoc = assoc;
    _priority = infixPriority;
  }

  /**
   * @return true, since all calculation symbols we currently consider are typically presented in
   * infix notation.
   */
  @Override
  public boolean isInfixSymbol() { return true; }

  /**
   * Determines if we should print brackets around the term underneath by default, based on the
   * priority and associativity.
   */
  @Override
  public boolean queryIncludeBrackets(FunctionSymbol subroot, int argument) {
    CalculationSymbol root = subroot.toCalculationSymbol();
    if (root == null) return false;
    if (root.equals(this)) {
      if (_assoc.equals(Associativity.ASSOC_LEFT) ||
          _assoc.equals(Associativity.ASSOC_LEFT_INCLUSIVE)) return argument != 1;
      if (_assoc.equals(Associativity.ASSOC_RIGHT)) return argument != 2;
    }
    else if (root.queryInfixPriority() == _priority &&
             _assoc.equals(Associativity.ASSOC_LEFT_INCLUSIVE)) return argument != 1;
    return _priority >= root.queryInfixPriority();
  }

  /** @return the kind of calculation symbol this is. */
  @Override
  public Kind queryKind() { return _kind; }

  /** @return the associativity of the current symbol. */
  @Override
  public Associativity queryAssociativity() { return _assoc; }

  /** @return the infix priority of the current symbol (or whatever if it is not infix). */
  @Override
  public int queryInfixPriority() { return _priority; }

  /** @return true, since calculation symbols are guaranteed to be theory symbols. */
  @Override
  public boolean isTheorySymbol() { return true; }

  /** @return true, since calculation symbols are theory terms */
  @Override
  public boolean isTheoryTerm() { return true; }

  /** @return false */
  @Override
  public boolean isValue() { return false; }

  /** @return this */
  @Override
  public CalculationSymbol toCalculationSymbol() { return this; }

  /** @return this, since a calculation symbol is not polymorphic, so substituting has no effect */
  @Override
  public FunctionSymbol substituteType(Type.ISubstitution typeMapping) { return this; }
}

