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

/**
 * This static class generates basic types and arrow types, which are otherwise not directly
 * accessible outside the types package.
 */
public class TypeFactory {
  /** The unit sort is the unique sort that is used for "unsorted" term rewriting. */
  public static BaseType unitSort = new Sort("o");

  /** Creates a basic type by the given name. */
  public static BaseType createSort(String name) {
    return new Sort(name);
  }

  /** Creates a type of the form left → right */
  public static Type createArrow(Type left, Type right) {
    return new ArrowType(left, right);
  }
}

