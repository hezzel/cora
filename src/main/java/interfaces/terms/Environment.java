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

import java.lang.Iterable;

/**
 * An Environment is a finite set of variables, which may later be equipped with additional data
 * such as which are free and which are bound.
 * It is used for instance to list the variables used in an individual term.
 */
public interface Environment extends Iterable<Variable> {
  /** Returns whether the given variable is an element of the environment. */
  boolean contains(Variable x);

  /** Adds the given variable to the environment, if it is not in there yet. */
  void add(Variable x);

  /** Returns the number of variables currently in the environment. */
  int size();

  /**
   * Returns a copy of the same Environment (since implementations of Environment are not
   * immutable).
   */
  Environment copy();
}

