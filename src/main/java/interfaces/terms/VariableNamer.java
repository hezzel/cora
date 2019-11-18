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
 * A VariableNamer is a class that assigns fresh names to variables, for use in pretty printing.
 *
 * VariableNamers keep track of the variables that have already been assigned a name, and are
 * mutable.
 */

public interface VariableNamer {
  /**
   * If the given variable x has already been assigned a name, this name is returned; if not,
   * null is returned instead.
   */
  String queryAssignedName(Variable x);

  /**
   * This selects a name for the given variable, avoiding names that have already been assigned
   * (or otherwise marked as inaccessible, such as names occurring in the alphabet).
   */
  String assignName(Variable x);
}

