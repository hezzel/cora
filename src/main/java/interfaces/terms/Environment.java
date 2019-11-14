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
 * An Environment is a finite set of variables, typically used to list the free (or bound)
 * variables used in a specific term or rule.
 *
 * Note: all instances of Environment must (and can be expected to) be immutable.
 */
public interface Environment extends Iterable<Variable> {
  /** Returns whether the given variable is an element of the environment. */
  boolean contains(Variable x);

  /** Returns whether the current environment contains all elements in the given other. */
  boolean containsAll(Environment other);

  /** Returns the number of variables currently in the environment. */
  int size();

  /** Adds the given variable to the environment and returns the result. */
  public Environment extend(Variable x);

  /** Removes the given variable from the environment and returns the result. */
  public Environment remove(Variable x);
}

