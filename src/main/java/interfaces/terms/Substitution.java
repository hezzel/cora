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

import java.util.Set;

/**
 * A substitution is a function that maps a finite set of variables to terms of the same type.
 *
 * A substitution is inherently a mutable structure, as entries may be added and removed.
 * Therefore, functions which take a substituion as argument should always indicate whether (and
 * how) the substitution is altered in the function.
 */
public interface Substitution {
  /** Returns the Term that x is mapped to, or null if x is not mapped to anything. */
  Term get(Variable x);

  /**
   * Returns the Term that x is mapped to, if anything, or a term representing the variable x if
   * x is not mapped to anything.
   */
  Term getReplacement(Variable x);

  /**
   * Update the substitution with the given key/value pair.
   * If there is already a mapping for key, this will return false and have no effect.
   * If the key and value do not have the same type, a TypingError will be thrown instead.
   */
  boolean extend(Variable key, Term value);

  /**
   * Update the substitution by replacing the current mapping for key (if any) by value.
   * If there was already a value for the given key, this will return true and replace; if there
   * was not, then this will return false and simply extend.  Either way the key/value pair becomes
   * part of the mapping!
   * If the key and value do not have the same type, a TypingError will be thrown instead.
   */
  boolean replace(Variable key, Term value);

  /**
   * Returns the set of variables which have a mapped variable, including those which are mapped
   * to themselves.
   */
  Set<Variable> domain();

  /** Remove the given key/value pair from the mapping. */
  void delete(Variable key);
}

