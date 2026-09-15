/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms.replaceable;

import charlie.types.TVarSet;
import charlie.types.Type;

/**
 * This class provides a minimal implementation of Replaceable.  It is used to test some of the
 * classes in charlie.terms.replaceable without introducing a dependency on things outside the
 * package (e.g., charlie.terms.Variable).  This avoids a circular dependency between packages.
 */
public class MyReplaceable implements Replaceable {
  int _index;
  String _name;
  Type _type;
  int _arity;
  private static int _counter = 0;

  MyReplaceable(String name, Type type, int arity) {
    _counter++;
    _index = _counter;
    _name = name;
    _type = type;
    _arity = arity;
  }

  public Kind queryReplaceableKind() { return _arity == 0 ? Kind.BASEVAR : Kind.METAVAR; }
  public String queryName() { return _name; }
  public Type queryType() { return _type; }
  public boolean isMonomorphic() { return _type.isMonomorphic(); }
  public int queryArity() { return _arity; }
  public int queryIndex() { return _index; }
  public boolean equals(Replaceable x) { return x.queryIndex() == _index; }
  public int compareTo(Replaceable x) { return _index - x.queryIndex(); }
  public TVarSet queryTypeVars() { return TVarSet.EMPTY; }
}
