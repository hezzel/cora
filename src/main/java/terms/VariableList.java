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

import java.util.Collection;
import java.util.Iterator;
import java.util.TreeSet;
import java.util.TreeMap;

/** An immutable collection of variables. */
public interface VariableList extends Iterable<Variable> {
  /** Returns whether the given variable is an element of the environment. */
  boolean contains(Variable x);

  /** Returns the number of variables currently in the environment. */
  int size();

  /**
   * Returns a unique name for all the variables in the list (since it is allowed for distinct
   * variables to have the same name).
   */
  TreeMap<Variable,String> getUniqueNaming();
}

