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

/** The binary conjunction operator ∧ or ∨. */
class AndOrSymbol extends CalculationInherit {
  private boolean _disjunction; // true if we are ∨, false if we are ∧

  AndOrSymbol(boolean isOr) {
    // Bool ⇒ Bool ⇒ Bool
    super(TypeFactory.createArrow(TypeFactory.boolSort, TypeFactory.createArrow(
      TypeFactory.boolSort, TypeFactory.boolSort)));
    _disjunction = isOr;
  }

  public String queryName() {
    if (_disjunction) return "∨";
    else return "∧";
  }

  public int queryArity() {
    return 2;
  }

  public String toUniqueString() {
    if (_disjunction) return "∨";
    else return "∧";
  }

  public int queryInfixPriority() {
    return CalculationSymbol.INFIX_ANDOR;
  }

  public boolean printInfix(StringBuilder builder, List<Term> args,
                            Map<Replaceable,String> renaming, Set<String> avoid) {
    if (args.size() != 2) return false; // let the standard printing procedure handle it
    
    // we are left-associative, so if the left component is the same symbol, it can be printed
    // without brackets
    Term left = args.get(0);
    if (left.isFunctionalTerm() && equals(args.get(0).queryRoot())) {
      left.addToString(builder, renaming, avoid);
    }
    else printHelper(builder, left, renaming, avoid, CalculationSymbol.INFIX_ANDOR);

    builder.append(" " + queryName() + " ");
    printHelper(builder, args.get(1), renaming, avoid, CalculationSymbol.INFIX_ANDOR);
    return true;
  }
}

