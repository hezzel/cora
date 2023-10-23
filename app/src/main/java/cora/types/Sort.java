/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

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

import java.util.List;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.InappropriatePatternDataError;

/**
 * A sort is an atomic type, identified as just a string.
 *
 * Note that Sort should not be used directly in the program.  Instead, use the Type or BaseType
 * interface, and the TypeFactory to create sorts.
 *
 * Sorts internally keep track whether they are a theory sort (which has some inherent meaning) or
 * a non-theory sort.  However, equality of sorts is just by name; it is not allowed to use both a
 * theory and non-theory sort of the same name in the same TRSs.
 */
class Sort implements BaseType {
  private String _name;
  private boolean _theorySort;

  Sort(String name, boolean theory) {
    if (name == null) throw new NullInitialisationError("Sort", "name");
    _name = name;
    _theorySort = theory;
  }

  /** @return true */
  public boolean isBaseType() { return true; }

  /** @return false */
  public boolean isArrowType() { return false; }

  /** @return whether this was created to be a theory sort or not */
  public boolean isTheorySort() { return _theorySort; }
  
  /** @return whether this was created to be a theory sort or not */
  public boolean isTheoryType() { return _theorySort; }

  /** Returns a string representation of this sort. */
  public String toString() {
    return _name;
  }

  /**
   * Checks equality with the given Type (exactly if it's a base type, and their toStrings are
   * equal).
   */
  public boolean equals(Type type) {
    return type != null && type.isBaseType() && _name.equals(type.toString());
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

  /** @return 0 */
  public int queryTypeOrder() { return 0; }

  /** Does nothing, as a base type does not have input types. */
  public void appendInputTypes(List<Type> answer) { }

  /** Do not call on BaseType -- results in an InappropriatePatternDataError. */
  public Type queryArrowInputType() {
    throw new InappropriatePatternDataError("BaseType", "queryArrowInputType", "arrow types");
  }

  /** Do not call on BaseType -- results in an InappropriatePatternDataError. */
  public Type queryArrowOutputType() {
    throw new InappropriatePatternDataError("BaseType", "queryArrowOutputType", "arrow types");
  }
}

