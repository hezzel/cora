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

/** The unary negation operator ¬. */
class NotSymbol extends CalculationInherit {
  NotSymbol() {
    super(TypeFactory.createArrow(TypeFactory.boolSort, TypeFactory.boolSort)); // Bool ⇒ Bool
  }

  public String queryName() {
    return "¬";
  }

  public int queryArity() {
    return 1;
  }

  public String toUniqueString() {
    return "¬";
  }

  public int queryInfixPriority() {
    return CalculationSymbol.INFIX_NOT;
  }

  public Value calculate(List<Term> args) {
    if (args.size() != 1) return null;
    if (!args.get(0).isValue()) return null;
    if (!args.get(0).queryType().equals(TypeFactory.boolSort)) return null;
    return new BooleanValue(!args.get(0).toValue().getBool());
  }

  public boolean printInfix(StringBuilder builder, List<Term> args,
                            Map<Replaceable,String> renaming, Set<String> avoid) {
    if (args.size() != 1) return false; // let the standard printing procedure handle it

    builder.append("¬");
    printHelper(builder, args.get(0), renaming, avoid, CalculationSymbol.INFIX_NOT);
    return true;
  }
}

