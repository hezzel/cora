/**************************************************************************************************
 Copyright 2022--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.types;

import java.util.List;
import charlie.util.FixedList;

/**
 * This static class generates base types, data types, arrow types and type variables, and can be
 * used to access the unique theory types which are tracked by the program.
 */
public class TypeFactory {
  /** The theory sort Int, representing the commonly used set of integer numbers. */
  public static final Base intSort = new Base("Int");

  /** The theory sort Bool, representing the set of boolean values {true, false}. */
  public static final Base boolSort = new Base("Bool");

  /** The theory sort String, representing the set of Strings. */
  public static final Base stringSort = new Base("String");

  /** The default sort, used for instance as the unique sort in "unsorted" term rewriting. */
  public static final Base defaultSort = new Base("o");

  /** Creates a basic type by the given name. */
  public static Base createSort(String name) {
    return new Base(name);
  }

  /** Creates a data type built from the given sort constructor and arguments. */
  public static Data createSort(String name, Type arg, Type ...moreArgs) {
    FixedList.Builder<Type> builder = new FixedList.Builder<Type>(moreArgs.length+1);
    builder.add(arg);
    for (Type t : moreArgs) builder.add(t);
    return new Data(name, builder.build());
  }

  /** Creates a base or data type built from the given sort constructor and arguments. */
  public static Type createSort(String name, List<Type> args) {
    if (args.isEmpty()) return new Base(name);
    else return new Data(name, FixedList.copy(args));
  }

  /** Creates a base or data type built from the given sort constructor and arguments. */
  public static Type createSort(String name, FixedList<Type> args) {
    if (args.isEmpty()) return new Base(name);
    else return new Data(name, args);
  }

  /** Creates a type of the form left → right */
  public static Type createArrow(Type left, Type right) {
    return new Arrow(left, right);
  }

  /** Creates a type variable by the given name (which should not include the starting $). */
  public static TVar createVariable(String name) {
    return new TVar(name);
  }

  /** Creates a type of the form inp_1 →...→ inp_n → output */
  public static Type createSortDeclaration(List<Base> inputs, Base output) {
    Type ret = output;
    for (int i = inputs.size()-1; i >= 0; i--) ret = new Arrow(inputs.get(i), ret);
    return ret;
  }

  /** Creates a type o → ... → o → o, with in total arity+1 os. */
  public static Type createDefaultArrow(int arity) {
    Type ret = defaultSort;
    for (int i = 0; i < arity; i++) ret = new Arrow(defaultSort, ret);
    return ret;
  }
}
