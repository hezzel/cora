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

package cora.terms;

import java.util.Collection;
import java.util.Iterator;
import java.util.TreeSet;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Environment;

/** Env is the default implementation of Environment: a set of variables with unique names. */
public class Env implements Environment {
  private TreeSet<Variable> _variables;

  public Env() {
    _variables = new TreeSet<Variable>();
  }

  public Env(Collection<Variable> vars) {
    _variables = new TreeSet<Variable>();
    for (Variable x : vars) add(x);
  }

  /**
   * Adds the given variable to the environment.
   * Throws an Error if a variable of the same name is already in the environment.
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

  /** Returns a copy of the current environment. */
  public Environment copy() {
    return new Env(_variables);
  }
}

