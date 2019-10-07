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
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.interfaces.types.*;

/** A type of the form σ ⇒ τ. */
public class ArrowType implements Type {
  private Type _left, _right;

  /** Creates the type left ⇒ right. */
  public ArrowType(Type left, Type right) {
    if (left == null) throw new NullInitialisationError("ArrowType", "input type");
    if (right == null) throw new NullInitialisationError("ArrowType", "output type");
    _left = left;
    _right = right;
  }

  /** @return false */
  public boolean isBaseType() { return false; }

  /** @return true */
  public boolean isArrowType() { return true; }

  /** Returns a string representation which takes right-associativity into account. */
  public String toString() {
    String leftstring = _left.toString();
    String rightstring = _right.toString();
    
    String left;
    if (_left.isArrowType()) left = "(" + leftstring + ")";
    else if (_left.isBaseType()) left = leftstring;
    else throw new Error("Missed a case in a switch for type kinds.");
    return left + " → " + rightstring;
  }

  public boolean equals(Type type) {
    if (type == null || !type.isArrowType()) return false;
    return _left.equals(type.queryArrowInputType()) &&
           _right.equals(type.queryArrowOutputType());
  }

  public int queryArity() {
    return 1 + _right.queryArity();
  }

  public BaseType queryOutputSort() {
    return _right.queryOutputSort();
  }

  public int queryTypeOrder() {
    int a = _left.queryTypeOrder() + 1;
    int b = _right.queryTypeOrder();
    return a > b ? a : b;
  }

  public void appendInputTypes(ArrayList<Type> answer) {
    answer.add(_left);
    _right.appendInputTypes(answer);
  }

  /** For a type σ ⇒ τ, returns σ. */
  public Type queryArrowInputType() {
    return _left;
  }

  /** For a type σ ⇒ τ, returns τ. */
  public Type queryArrowOutputType() {
    return _right;
  }
}

