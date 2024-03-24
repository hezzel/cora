/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

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

/**
 * This class keeps track of a number of important types Cora uses for specific
 * purposes, like the pre-defined theory types.
 */
final class UniqueTypes {
  // This class should not be instantiated
  private UniqueTypes() {}

  /** Returns the sort used to represent the set of integers. */
  public static final Base intSort = new Base("Int");

  /** Returns the sort used to represent the set of booleans. */
   public static final Base boolSort = new Base("Bool");

  /** Returns the sort used to represent the set of strings. */
  public static final Base stringSort = new Base("String");

  /** 
   * Returns the default sort.
   * This is not a theory sort, but used for instance as the one sort in unsorted first-order TRSs.
   */
  public static final Base defaultSort = new Base("o");

  static boolean isTheoryType(Type ty) {
    return
      ty == UniqueTypes.intSort  ||
      ty == UniqueTypes.boolSort ||
      ty == TypeFactory.stringSort;
  }
}
