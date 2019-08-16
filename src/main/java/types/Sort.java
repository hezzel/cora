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

package cora.types;

import java.util.ArrayList;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.InappropriatePatternDataError;
import cora.interfaces.types.*;

/** A sort is an atomic type, identified as just a string. */
public class Sort implements BaseType {
  private String _name;

  public Sort(String name) {
    if (name == null) throw new NullInitialisationError("Sort", "name");
    _name = name;
  }

  /** @return BASETYPE */
  public Type.TypeKind queryTypeKind() {
    return Type.TypeKind.BASETYPE;
  }

  /** Returns a string representation of this sort. */
  public String toString() {
    return _name;
  }

  /**
   * Checks equality with the given Type (exactly if it's a base type, and their toStrings are
   * equal).
   */
  public boolean equals(Type type) {
    return type.queryTypeKind() == Type.TypeKind.BASETYPE &&
           _name.equals(type.toString());
  }

  /** Checks equality with the given base type (exactly if their toStrings are equal). */
  public boolean equals(BaseType sort) {
    return _name.equals(sort.toString());
  }

  /** @return 0 */
  public int queryArity() {
    return 0;
  }
  
  /** @return this */
  public BaseType queryOutputSort() { return this; }

  /** Does nothing, as a base type does not have input types. */
  public void appendInputTypes(ArrayList<Type> answer) { }

  /** Do not call on BaseType -- results in an InappropriatePatternDataError. */
  public Type queryArrowInputType() {
    throw new InappropriatePatternDataError("BaseType", "queryArrowInputType", "arrow types");
  }

  /** Do not call on BaseType -- results in an InappropriatePatternDataError. */
  public Type queryArrowOutputType() {
    throw new InappropriatePatternDataError("BaseType", "queryArrowOutputType", "arrow types");
  }
}

