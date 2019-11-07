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

package cora.terms;

import cora.types.Sort;

/**
 * A UnitVariable is a free variable whose type is the unit sort.
 * It can be used in analysis of unsorted first-order term rewriting.
 */
public class UnitVariable extends Var {
  /** Create a unit variable with the given name. */
  public UnitVariable(String name) {
    super(name, Sort.unitSort);
  }

  /** Create a unit variable without a name; a name will be automatically generated. */
  public UnitVariable() {
    super(Sort.unitSort);
  }
}

