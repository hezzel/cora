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

/** The unary minus operator -. */
class MinusSymbol extends CalculationInherit {
  MinusSymbol() {
    super(TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.intSort)); // Int → Int
  }

  public String queryName() {
    return "-";
  }

  public int queryArity() {
    return 1;
  }

  public String toUniqueString() {
    return "-";
  }

  public int queryInfixPriority() {
    return CalculationSymbol.INFIX_MINUS;
  }

  public boolean printInfix(StringBuilder builder, List<Term> args,
                            Map<Replaceable,String> renaming, Set<String> avoid) {
    if (args.size() != 1) return false; // let the standard printing procedure handle it

    builder.append("-");
    Term arg = args.get(0);
    if (arg.isValue()) {
      int k = arg.toValue().getInt();
      if (k < 0) builder.append("(" + k + ")");
      else builder.append("" + k);
    }
    else printHelper(builder, arg, renaming, avoid, CalculationSymbol.INFIX_MINUS);
    return true;
  }
}

