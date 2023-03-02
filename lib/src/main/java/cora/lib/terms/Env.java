/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.lib.terms;

import java.lang.Iterable;
import java.util.Iterator;
import java.util.TreeSet;

/**
 * Env is the default implementation of Environment: a set of variables with not-necessarily-unique
 * names.
 */
class Env implements Environment {
  private TreeSet<Variable> _variables;

  /**
   * Constructs an empty environment. (Default because it should only be created from inside the
   * terms package, for example the factory.)
   */
  Env() {
    _variables = new TreeSet<Variable>();
  }

  /**
   * Constructs an environment containing the given variables. (Default because it should only be
   * created from inside the terms package, for example the factory.)
   *
   * Note that both Environment and VarList are iterables, so can be used as an argument.
   */
  Env(Iterable<Variable> vars) {
    _variables = new TreeSet<Variable>();
    for (Variable x : vars) add(x);
  }

  /**
   * Adds the given variable to the environment.
   * Does nothing if a variable of the same name is already in the environment.
   */
  public void add(Variable x) {
    _variables.add(x);
  }

  /** Returns whether the given variable is an element of the environment. */
  public boolean contains(Variable x) {
    return _variables.contains(x);
  }

  /** Returns the number of variables in this environment. */
  public int size() {
    return _variables.size();
  }

  /** Returns an iterator over all variables in the environment. */
  public Iterator<Variable> iterator() {
    return _variables.iterator();
  }

  /** Returns the VarList corresponding to the current environment. */
  public VarList getImmutableCopy() {
    return new VarList(_variables);
  }

  /** Returns a copy of the current environment. */
  public Environment copy() {
    return new Env(_variables);
  }
}

