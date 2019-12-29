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

import java.util.TreeMap;
import java.util.TreeSet;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.VariableNamer;
import cora.interfaces.terms.Environment;
import cora.interfaces.terms.Alphabet;

/**
 * This class assigns a unique name to each variable, and keeps track of the variables that have
 * already been assigned.
 */
public class CleverVariableNamer implements VariableNamer {
  private TreeMap<Variable,String> _variableToName;
  private TreeSet<String> _chosenNames;
  private Alphabet _alphabet;

  /** Creates a variable namer without any pre-assignments. */
  public CleverVariableNamer() {
    _alphabet = null;
    _chosenNames = new TreeSet<String>();
    _variableToName = new TreeMap<Variable,String>();
  }

  /**
   * Creates a variable namer without any pre-assignments, but that will avoid assigning any names
   * in the given alphabet.
   */
  public CleverVariableNamer(Alphabet sigma) {
    _alphabet = sigma;
    _chosenNames = new TreeSet<String>();
    _variableToName = new TreeMap<Variable,String>();
  }

  /**
   * Creates a variable namer that (a) will avoid all names in the given alphabet, and
   * (b) pre-assigns the variables in the given environment to their given names, insofar as
   * there are no overlaps. When there are overlaps, the variable with the lower index is the one
   * that keeps its name.
   */
  public CleverVariableNamer(Alphabet sigma, Environment tryToKeepThese) {
    _alphabet = sigma;
    _chosenNames = new TreeSet<String>();
    _variableToName = new TreeMap<Variable,String>();
    
    TreeMap<String,Variable> nametovar = new TreeMap<String,Variable>();
    for (Variable x : tryToKeepThese) {
      String name = x.queryName();
      if (name == null) continue;
      if (_alphabet != null && _alphabet.lookup(name) != null) continue;
      if (nametovar.get(name) == null || nametovar.get(name).compareTo(x) > 0) {
        nametovar.put(name, x);
      }
    }

    for (Variable var : nametovar.values()) {
      _variableToName.put(var, var.queryName());
      _chosenNames.add(var.queryName());
    }
  }

  public String queryAssignedName(Variable x) {
    return _variableToName.get(x);
  }

  private boolean nameIsAvailable(String name) {
    if (_alphabet != null && _alphabet.lookup(name) != null) return false;
    return !_chosenNames.contains(name);
  }

  private String selectEntirelyNewName(Variable var) {
    String[] options;
    if (var.queryType().isBaseType()) {
      if (var.isBinderVariable()) {
        options = new String[] { "x", "y", "z", "u", "v", "w", "n", "m", "a", "b" };
      }
      else {
        options = new String[] { "X", "Y", "Z", "U", "V", "W", "N", "M", "A", "B" };
      }
    }
    else {
      if (var.isBinderVariable()) {
        options = new String[] { "f", "g", "h", "i", "j", "k", "l", "p", "q", "r" };
      }
      else {
        options = new String[] { "F", "G", "H", "I", "J", "K", "L", "P", "Q", "R" };
      }
    }

    for (String option : options) {
      if (nameIsAvailable(option)) return option;
    }
    
    for (int i = 1; ; i++) {
      String name = "var" + i;
      if (nameIsAvailable(name)) return name;
    }
  }

  public String assignName(Variable x) {
    String chosen = _variableToName.get(x);
    if (chosen != null) return chosen;

    String name = x.queryName();
    if (name == null) name = selectEntirelyNewName(x);
    else {
      while (!nameIsAvailable(name)) name = name + "'";
    }

    _variableToName.put(x, name);
    _chosenNames.add(name);
    return name;
  }
}

