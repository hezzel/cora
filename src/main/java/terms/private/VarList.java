/**************************************************************************************************
 Copyright 2023 Cynthia Kop

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

/**
 * VarList is the default implementation of VariableList: an immutable set of variables with
 * not-necessarily-unique names.
 */
class VarList implements VariableList {
  private TreeSet<Variable> _variables;
  public static VarList EMPTY = new VarList();

  /** Constructs the empty varlist */
  private VarList() {
    _variables = new TreeSet<Variable>();
  }

  /** Constructs the varlist with a copy of the given variables. */
  VarList(Collection<Variable> vars) {
    _variables = new TreeSet<Variable>(vars);
  }

  /**
   * Constructs the varlist with the given variables, which become the property of this VarList.
   * The second variable is a dummy, to clearly distinguish between this constructor and the
   * other one.
   */
  VarList(TreeSet<Variable> vars, boolean dummy) {
    _variables = vars;
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
}

