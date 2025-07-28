/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import charlie.util.FixedList;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TypeFactory;

/**
 * This class is for Meta-variables of higher type; that is, arity ≥ 1.
 */
final class HigherMetaVar implements MetaVariable {
  private static int _COUNTER = 0;
  private final String _name;
  private final FixedList<Type> _inputs;
  private final Type _output;
  private final int _index;
  private Type _mytype;

  HigherMetaVar(String name, FixedList<Type> inputs, Type output) {
    _name = name;
    _inputs = inputs;
    _output = output;
    _index = _COUNTER;
    _COUNTER++;
    if (name == null) throw new NullStorageException("HigherMetaVar", "name");
    if (inputs == null) throw new NullStorageException("HigherMetaVar", "inputs");
    if (output == null) throw new NullStorageException("HigherMetaVar", "output");
    if (inputs.size() == 0) {
      throw new IllegalArgumentException("HigherMetaVar::constructor -- empty inputs list " +
        "given: a meta-variable without arguments should be constructed as a Var instead.");
    }
    _mytype = _output;
    for (int i = _inputs.size()-1; i >= 0; i--) {
      _mytype = TypeFactory.createArrow(_inputs.get(i), _mytype);
    }
  }

  public String queryName() {
    return _name;
  }

  public int queryIndex() {
    return _index;
  }

  public int queryArity() {
    return _inputs.size();
  }

  public Kind queryReplaceableKind() {
    return Replaceable.Kind.METAVAR;
  }

  public Type queryInputType(int i) {
    if (i <= 0 || i > _inputs.size()) {
      throw new IndexOutOfBoundsException("HigherMetaVar::queryInputType(" + i + ") called on " +
        "meta-variable with arity " + _inputs.size() + ".");
    }
    return _inputs.get(i-1);
  }

  public Type queryOutputType() {
    return _output;
  }

  public Type queryType() {
    return _mytype;
  }

  public int compareTo(Replaceable other) {
    if (other == this) return 0;    // shortcut
    int d = other.queryReplaceableKind().compareTo(queryReplaceableKind());
    if (d != 0) return d;
    d = _index - other.queryIndex();
    if (d != 0) return d;
    d = _inputs.size() - other.queryArity();
    if (d != 0) return d;
    // we really shouldn't get here, but just in case...
    return _mytype.toString().compareTo(other.queryType().toString());
  }

  /** Two replaceables are equal if and only if they are the same object. */
  public boolean equals(Replaceable other) {
    return other == this;
  }

  /** Returns a hashcode that (uniquely) identifies this meta-variable */
  public int hashCode() {
    return 3 * _index + 2;
  }

  public String toString() {
    return _name;
  }
}
