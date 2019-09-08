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

import java.lang.Comparable;
import cora.interfaces.types.Type;

/**
 * Variables are both used as parts of constraints, as binders in an abstraction, as generic
 * expression in terms and as open spots for matching in rules.
 * Multiple distinct variables are allowed to share the same name.  In practice, this name is used
 * to define the basis of the actual variable name in pretty printing.  Thus, variables are not
 * defined by their name, but rather an internally kept index.
 *
 * Note: all instances of Variable must (and can be expected to) be immutable.
 */
public interface Variable extends Term, Comparable<Variable> {
  /**
   * @return a string representation of the variable.
   * Variable names are not unique, and variables are not identified by their name.
   */
  String queryName();

  /** @return the type of the variable */
  Type queryType();

  /** @return equality to another Variable */
  boolean equals(Variable x);

  /** A variable is uniquely defined by its ID (two Variables are equal iff they share indexes). */
  int queryVariableIndex();
}

