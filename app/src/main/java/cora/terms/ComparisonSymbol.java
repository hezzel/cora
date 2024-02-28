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

import java.util.List;
import java.util.Map;
import java.util.Set;

import cora.types.TypeFactory;

/** One of the binary relations <, >, ≤, ≥. */
class ComparisonSymbol extends CalculationInherit {
  static final String KIND_GRE = ">";
  static final String KIND_SMA = "<";
  static final String KIND_GEQ = "≥";
  static final String KIND_LEQ = "≤";
  static final String KIND_EQU = "=";
  static final String KIND_NEQ = "≠";
  private final String _kind;

  ComparisonSymbol(String kind) {
    // Int → Int → Bool
    super(TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.createArrow(
      TypeFactory.intSort, TypeFactory.boolSort)));
    _kind = kind; // the factory should ensure this is only called with appropriate kinds
  }

  public String queryName() {
    return _kind;
  }

  public int queryArity() {
    return 2;
  }

  public String toUniqueString() {
    return _kind;
  }

  public Kind queryKind() {
    if (_kind.equals(KIND_GRE)) return Kind.GREATER;
    if (_kind.equals(KIND_SMA)) return Kind.SMALLER;
    if (_kind.equals(KIND_GEQ)) return Kind.GEQ;
    if (_kind.equals(KIND_LEQ)) return Kind.LEQ;
    if (_kind.equals(KIND_EQU)) return Kind.EQUALS;
    if (_kind.equals(KIND_NEQ)) return Kind.NEQ;
    throw new Error("Unknown comparison kind: " + _kind);
  }

  public int queryInfixPriority() {
    return CalculationSymbol.INFIX_COMPARISON;
  }

  public Associativity queryAssociativity() {
    return Associativity.ASSOC_NONE;
  }
}
