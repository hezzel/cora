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
import java.util.List;
import java.util.TreeSet;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Environment;

/**
 * Env is the default implementation of Environment: a set of variables with not necessarily unique
 * names.
 */
public class Env implements Environment {
  private TreeSet<Variable> _variables;

  public Env() {
    _variables = new TreeSet<Variable>();
  }

  public Env(Variable x) {
    _variables = new TreeSet<Variable>();
    _variables.add(x);
  }

  public Env(List<Environment> others) {
    _variables = new TreeSet<Variable>();
    for (Environment e : others) {
      for (Variable x : e) {
        _variables.add(x);
      }
    }
  }

  public Env(Collection<Variable> vars) {
    _variables = new TreeSet<Variable>();
    for (Variable x : vars) _variables.add(x);
  }

  /** Returns whether the given variable is an element of the environment. */
  public boolean contains(Variable x) {
    return _variables.contains(x);
  }

  /** Returns whether the current environment contains all variables in the given other. */
  public boolean containsAll(Environment other) {
    for (Variable x : other) {
      if (!_variables.contains(x)) return false;
    }
    return true;
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

  /** Adds the given variable to the environment and returns the result. */
  public Environment extend(Variable x) {
    Env other = new Env(_variables);
    other._variables.add(x);
    return other;
  }

  /** Removes the given variable from the environment and returns the result. */
  public Environment remove(Variable x) {
    Env other = new Env(_variables);
    other._variables.remove(x);
    return other;
  }
}

