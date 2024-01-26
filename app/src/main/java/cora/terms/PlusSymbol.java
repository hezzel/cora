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

/** The binary addition symbol +. */
class PlusSymbol extends CalculationInherit {
  PlusSymbol() {
    // Int → Int → Int
    super(TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.createArrow(
      TypeFactory.intSort, TypeFactory.intSort)));
  }

  public String queryName() {
    return "+";
  }

  public int queryArity() {
    return 2;
  }

  public String toUniqueString() {
    return "+";
  }

  public int queryInfixPriority() {
    return CalculationSymbol.INFIX_PLUS;
  }

  public boolean printInfix(StringBuilder builder, List<Term> args,
                            Map<Replaceable,String> renaming, Set<String> avoid) {
    if (args.size() != 2) return false; // let the standard printing procedure handle it
    printHelper(builder, args.get(0), renaming, avoid, CalculationSymbol.INFIX_PLUS-1);
    Term right = args.get(1);
    if (right.isValue()) {
      int k = right.toValue().getInt();
      if (k < 0) builder.append(" - " + (-k));
      else builder.append(" + " + k);
    }
    else if (right.isFunctionalTerm() && right.numberArguments() == 1 &&
             right.queryHead() instanceof MinusSymbol) {
      builder.append(" - ");
      printHelper(builder, right.queryArgument(1), renaming, avoid, CalculationSymbol.INFIX_PLUS);
    }
    else {
      builder.append(" + ");
      printHelper(builder, right, renaming, avoid, CalculationSymbol.INFIX_PLUS);
    }
    return true;
  }
}

