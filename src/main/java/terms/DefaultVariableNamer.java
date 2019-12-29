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

import java.util.TreeSet;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.VariableNamer;

/**
 * This class assigns to each variable its own string representation, which is not necessarily
 * unique.
 * This is used to implement the default toString() behaviour of terms.
 */
class DefaultVariableNamer implements VariableNamer {
  private TreeSet<Variable> _known;

  public DefaultVariableNamer() {
    _known = new TreeSet<Variable>();
  }

  public String queryAssignedName(Variable x) {
    if (_known.contains(x)) return x.toString();
    else return null;
  }

  public String assignName(Variable x) {
    _known.add(x);
    return x.toString();
  }
}

