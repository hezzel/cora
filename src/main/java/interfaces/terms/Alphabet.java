/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.interfaces.terms;

/**
 * An Alphabet is a (possibly infinite) set of function symbols, which does not have any duplicate
 * name uses.
 * It is used for recognising (and typing) function symbols in various kinds of input.
 */
public interface Alphabet {
  /**
   * Returns the FunctionSymbol with the given name (there should be at most one) if it exists,
   * otherwise returns null.
   */
  FunctionSymbol lookup(String name);

  /**
   * Returns a copy of the same alphabet (since implementations of Alphabet are not necessarily
   * immutable).
   */
  Alphabet copy();
}

