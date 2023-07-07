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

import java.util.ArrayList;
import cora.exceptions.IndexingError;
import cora.exceptions.IllegalArgumentError;
import cora.exceptions.NullInitialisationError;
import cora.types.Type;
import cora.types.TypeFactory;

/**
 * This class is for Meta-variables of higher type; that is, arity ≥ 1.
 */
class HigherMetaVar implements MetaVariable {
  private static int _COUNTER = 0;
  private String _name;
  private ArrayList<Type> _inputs;
  private Type _output;
  private int _index;

  HigherMetaVar(String name, ArrayList<Type> inputs, Type output) {
    _name = name;
    _inputs = inputs;
    _output = output;
    _index = _COUNTER;
    _COUNTER++;
    if (name == null) throw new NullInitialisationError("HigherMetaVar", "name");
    if (inputs == null) throw new NullInitialisationError("HigherMetaVar", "inputs");
    if (output == null) throw new NullInitialisationError("HigherMetaVar", "output");
    for (int i = 0; i < inputs.size(); i++) {
      if (inputs.get(i) == null) {
        throw new NullInitialisationError("HigherMetaVar", "inputs[" + i + "]");
      }
    }
    if (inputs.size() == 0) {
      throw new IllegalArgumentError("HigherMetaVar", "constructor",
        "empty inputs list given: a meta-variable without arguments should be constructed as " +
        "a Var instead.");
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

  public int queryReplaceableKind() {
    return Replaceable.KIND_METAVAR;
  }

  public Type queryInputType(int i) {
    if (i <= 0 || i > _inputs.size()) throw new IndexingError("HigherMetaVar", "queryInputType",
      i, 1, _inputs.size());
    return _inputs.get(i-1);
  }

  public Type queryOutputType() {
    return _output;
  }

  public Type queryType() {
    Type ret = _output;
    for (int i = _inputs.size()-1; i >= 0; i--) ret = TypeFactory.createArrow(_inputs.get(i), ret);
    return ret;
  }

  public int compareTo(Replaceable other) {
    if (other == this) return 0;    // shortcut
    int d = other.queryReplaceableKind() - queryReplaceableKind();
    if (d != 0) return d;
    d = _index - other.queryIndex();
    if (d != 0) return d;
    d = _inputs.size() - other.queryArity();
    if (d != 0) return d;
    // we really shouldn't get here, but just in case...
    return queryType().toString().compareTo(other.queryType().toString());
  }

  /** Two replaceables are equal if and only if they are the same object. */
  public boolean equals(Replaceable other) {
    return other == this;
  }

  public String toString() {
    return _name;
  }
}

