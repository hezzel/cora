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

/** CalculationSymbols are symbols in the theory signature that can perform a computation. */
public interface CalculationSymbol extends FunctionSymbol {
  public static int INFIX_ANDOR = 1;
  public static int INFIX_COMPARISON = 2;
  public static int INFIX_NOT = 3;
  public static int INFIX_PLUS = 4;
  public static int INFIX_TIMES = 5;
  public static int INFIX_DIVMOD = 5;
  public static int INFIX_MINUS = 6;
  public static int INFIX_NONE = 0;

  /**
   * Used for printing: if symbols # and $ are printed infix (or otherwise in a special way), then
   * x # y $ z is meant as (x # y) $ z if # has higher infix priority, and as x # (y $ z) if $ has
   * higher priority.  If they have the same priority, this is not allowed unless # and $ are the
   * same symbol, which is either left- or right-associative.
   * Symbols that are not printed in a special way should return 0 for infix priority.
   */
  public int queryInfixPriority();

  /**
   * If this is a function symbol that should be printed in infix notation for the given number of
   * arguments, this function call will add the thus-printed term to the given string builder and
   * return true.  If not, false will be returned.  The arguments will not be altered in any way.
   * Objects calling this function should make sure the arguments fit the type of the function
   * symbol.
   */
  public boolean printInfix(StringBuilder builder, List<Term> args,
                            Map<Replaceable,String> renaming, Set<String> avoid);
}

