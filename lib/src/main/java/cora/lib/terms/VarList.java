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

package cora.lib.terms;

import java.util.Collection;
import java.util.Iterator;
import java.util.TreeSet;
import java.util.TreeMap;

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

  /** Constructors the varlist with just the given variable */
  public VarList(Variable x) {
    _variables = new TreeSet<Variable>();
    _variables.add(x);
  }

  /** Constructs the varlist with a copy of the given variables. */
  VarList(Collection<Variable> vars) {
    _variables = new TreeSet<Variable>(vars);
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

  /** Returns a copy of this list with the given variable added. */
  public VarList add(Variable x) {
    if (_variables.contains(x)) return this;
    VarList ret = new VarList(_variables);
    ret._variables.add(x);
    return ret;
  }

  /** Returns a copy of this list with the given variable removed. */
  public VarList remove(Variable x) {
    if (!_variables.contains(x)) return this;
    VarList ret = new VarList(_variables);
    ret._variables.remove(x);
    return ret;
  }

  /** Returns a combination of the current list with the given list. */
  public VariableList combine(VariableList other) {
    if (size() < other.size()) return other.combine(this);
    VarList ret = null;
    for (Variable x : other) {
      if (_variables.contains(x)) continue;
      if (ret == null) ret = new VarList(_variables);
      ret._variables.add(x);
    }
    if (ret == null) return this;
    return ret;
  }

  /** Returns the set of Variables that occur both in this list and the given iterable. */
  public TreeSet<Variable> getOverlap(Iterable<Variable> other) {
    TreeSet<Variable> ret = new TreeSet<Variable>();
    for (Variable x : other) {
      if (_variables.contains(x)) ret.add(x);
    }
    return ret;
  }

  /** Returns a mapping with a unique name for every variable in the term. */
  public TreeMap<Variable,String> getUniqueNaming() {
    // determine if any variable names occur more than once
    TreeMap<String,TreeSet<Variable>> map = new TreeMap<String,TreeSet<Variable>>();
    for (Variable x : _variables) {
      String name = x.queryName();
      if (!map.containsKey(name)) {
        TreeSet<Variable> vars = new TreeSet<Variable>();
        vars.add(x);
        map.put(name, vars);
      }
      else map.get(name).add(x);  // variable occurs more than once!
    }
    TreeMap<Variable,String> renaming = new TreeMap<Variable,String>();
    // for any that do, come up with new names; for any that don't, use the default name
    for (TreeSet<Variable> set : map.values()) {
      if (set.size() == 1) {
        Variable x = set.first();
        renaming.put(x, x.queryName());
      }
      else {
        int counter = 1;
        for (Variable x : set) {
          String name = x.queryName() + "__" + counter;
          counter++;
          for (; map.containsKey(name); counter++) name = x.queryName() + "__" + counter;
          renaming.put(x, name);
        }
      }
    }
    return renaming;
  }
}

