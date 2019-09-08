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
 * An Environment is a finite set of variables, each with a distinct name.
 * It is used for instance to list the variables used in an individual term.
 */
public interface Environment extends Iterable<Variable> {
  /**
   * Returns the Variable with the given name (there should be at most one) if it exists,
   * otherwise returns null.
   */
  Variable lookupName(String name);

  /** Returns whether the given variable is an element of the environment. */
  boolean contains(Variable x);

  /**
   * Adds the given variable to the environment, or throws an error if a variable by that name
   * (except for x itself) is already in the environment.
   */
  void add(Variable x);

  /**
   * Returns a copy of the same Environment (since implementations of Environment are not
   * immutable).
   */
  Environment copy();
}

