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
import cora.interfaces.rewriting.Alphabet;

/**
 * This class assigns a unique name to each variable, and keeps track of the variables that have
 * already been assigned.
 */
public class DefaultVariableNamer implements VariableNamer {
  private TreeMap<Variable,String> _variableToName;
  private TreeSet<String> _chosenNames;
  private Alphabet _alphabet;

  public DefaultVariableNamer(Alphabet sigma) {
    _alphabet = sigma;
    _chosenNames = new TreeSet<String>();
    _variableToName = new TreeMap<Variable,String>();
  }

  public DefaultVariableNamer() {
    _alphabet = null;
    _chosenNames = new TreeSet<String>();
    _variableToName = new TreeMap<Variable,String>();
  }

  public String queryAssignedName(Variable x) {
    return _variableToName.get(x);
  }

  public boolean nameIsAvailable(String name) {
    if (_alphabet != null && _alphabet.lookup(name) != null) return false;
    return !_chosenNames.contains(name);
  }

  public String selectEntirelyNewName() {
    String[] options = { "x", "y", "z", "u", "v", "w", "n", "m", "a", "b" };
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
    if (name == null) name = selectEntirelyNewName();
    else {
      while (!nameIsAvailable(name)) name = name + "'";
    }

    _variableToName.put(x, name);
    _chosenNames.add(name);
    return name;
  }
}

