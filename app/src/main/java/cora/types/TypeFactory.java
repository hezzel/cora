/**************************************************************************************************
 Copyright 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.types;

import java.util.List;

/**
 * This static class generates basic types and arrow types, which are otherwise not directly
 * accessible outside the types package.
 */
public class TypeFactory {
  /** The theory sort Int, representing the set of integer numbers. */
  public static BaseType intSort = new Sort("Int", true);
  /** The theory sort Bool, representing the set of boolean values {true, false}. */
  public static BaseType boolSort = new Sort("Bool", true);
  /** The theory sort String, representing the set of Strings. */
  public static BaseType stringSort = new Sort("String", true);
  /** The unit sort is the unique sort that is used for "unsorted" term rewriting. */
  public static BaseType unitSort = new Sort("o", false);

  /** Creates a basic (non-theory) type by the given name. */
  public static BaseType createSort(String name) {
    return new Sort(name, false);
  }

  /** Creates a type of the form inp_1 ⇒...⇒ inp_n → output */
  public static Type createSortDeclaration(List<BaseType> inputs, BaseType output) {
    Type ret = output;
    for (int i = inputs.size()-1; i >= 0; i--) ret = new ArrowType(inputs.get(i), ret);
    return ret;
  }

  /** Creates a type of the form left ⇒ right */
  public static Type createArrow(Type left, Type right) {
    return new ArrowType(left, right);
  }
}

