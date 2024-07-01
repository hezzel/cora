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

package charlie.terms;

import java.lang.Iterable;

/**
 * An Environment is a finite set of objects -- specifically, variables or meta-variables.
 * It is used for instance to list the variables used in an individual term.
 */
public interface Environment<T> extends Iterable<T> {
  /** Returns whether the given (meta-)variable is an element of the environment. */
  boolean contains(T x);

  /** Returns the number of elements in the environment.  Note: calling this takes linear time. */
  int size();
}
