/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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

/**
 * Variables are both used as parts of constraints, as binders in an abstraction, as generic
 * expression in terms and as open spots for matching in rules.
 *
 * There are two kinds of variables: binder variables and non-binder variables.  The former are
 * used as binders in abstraction; the latter are used for matching.  In true terms, both can be
 * used as free variables.
 *
 * Multiple distinct variables are allowed to share the same name.  In practice, this name is
 * intended to be used to define the basis of the actual variable name in pretty printing (although
 * it is also used directly in printing).  Thus, variables are not defined by their name, but
 * rather by an internally kept index.
 *
 * Note: all instances of Variable must (and can be expected to) be immutable.
 */
public interface Variable extends Term, Replaceable {
  /**
   * @return a string representation of the variable.
   * Variable names are not unique, and variables are not identified by their name.
   */
  String queryName();

  /** @return equality to another Variable */
  boolean equals(Variable x);

  /** Returns true if this is a binder variable, false if it is a non-binder variable. */
  public boolean isBinderVariable();
}

