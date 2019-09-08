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
import java.util.TreeMap;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Environment;
import cora.exceptions.NullCallError;

/** Env is the default implementation of Environment: a set of variables with unique names. */
public class Env implements Environment {
  private TreeMap<String,Variable> _variables;

  public Env() {
    _variables = new TreeMap<String,Variable>();
  }

  public Env(Collection<Variable> vars) {
    _variables = new TreeMap<String,Variable>();
    for (Variable x : vars) add(x);
  }

  /**
   * Adds the given variable to the environment.
   * Throws an Error if a variable of the same name is already in the environment.
   */
  public void add(Variable x) {
    Variable var = _variables.get(x.queryName());
    if (var != null && !var.equals(x)) {
      throw new Error("Trying to add variable with name " + x.queryName() + " to an environment " +
        "that already contains a different variable of the same name.");
    }
    _variables.put(x.queryName(), x);
  }

  /** Returns whether the given variable is an element of the environment. */
  public boolean contains(Variable x) {
    if (x == null) throw new NullCallError("Env", "contains", "variable x");
    Variable y = _variables.get(x.queryName());
    if (y == null) return false;
    return x.equals(y);
  }

  /**
   * Returns the variable with the give name in the environment, if any; if there is no such
   * variable, null is returned instead.
   */
  public Variable lookupName(String name) {
    return _variables.get(name);
  }

  /** Returns an iterator over all variables in the environment. */
  public Iterator<Variable> iterator() {
    return _variables.values().iterator();
  }

  /** Returns a copy of the current environment. */
  public Environment copy() {
    return new Env(_variables.values());
  }
}

