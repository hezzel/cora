/**************************************************************************************************
 Copyright 2022, 2023 Cynthia Kop

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

import com.google.common.collect.ImmutableList;
import java.util.List;

/**
 * This static class generates basic types, product types and arrow types, and can be used to
 * access the unique theory types which are tracked by the program.
 */
public class TypeFactory {
  /** The theory sort Int, representing the set of integer numbers. */
  public static final Base intSort = UniqueTypes.intSort;

  /** The theory sort Bool, representing the set of boolean values {true, false}. */
  public static final Base boolSort = UniqueTypes.boolSort;

  /** The theory sort String, representing the set of Strings. */
  public static final Base stringSort = UniqueTypes.stringSort;

  /** The unit sort is the unique sort that is used for "unsorted" term rewriting. */
  public static final Base unitSort = UniqueTypes.unitSort;

  /** Creates a basic (non-theory) type by the given name. */
  public static Base createSort(String name) { return new Base(name); }

  /** Creates a type of the form left ⇒ right */
  public static Type createArrow(Type left, Type right) { return new Arrow(left, right); }
  
  /** Creates a product type from the given list. */
  public static Type createProduct(ImmutableList<Type> types) {
    return new Product(types);
  }

  /** Creates a product type using a copy of the given list. */
  public static Type createProduct(List<Type> types) {
    return new Product(ImmutableList.copyOf(types));
  }

  /** Creates a product type arg1 x arg2 */
  public static Type createProduct(Type arg1, Type arg2) {
    ImmutableList.Builder builder = ImmutableList.builder();
    builder.add(arg1);
    builder.add(arg2);
    return new Product(builder.build());
  }

  /** Creates a product type arg1 x arg2 x arg3 */
  public static Type createProduct(Type arg1, Type arg2, Type arg3) {
    ImmutableList.Builder builder = ImmutableList.builder();
    builder.add(arg1);
    builder.add(arg2);
    builder.add(arg3);
    return new Product(builder.build());
  }

  /** Creates a type of the form inp_1 ⇒...⇒ inp_n → output */
  public static Type createSortDeclaration(List<Base> inputs, Base output) {
    Type ret = output;
    for (int i = inputs.size()-1; i >= 0; i--) ret = new Arrow(inputs.get(i), ret);
    return ret;
  }

}
