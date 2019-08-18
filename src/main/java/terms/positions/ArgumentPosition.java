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

package cora.terms.positions;

import cora.interfaces.terms.Position;
import cora.exceptions.NullInitialisationError;

/**
 * An ArgumentPosition is a position of the form i.pos, where i indicates the index of an argument
 * in the corresponding term and pos a position within that argument.
 */
public class ArgumentPosition implements Position {
  private int _argPos;
  private Position _tail;

  public ArgumentPosition(int argumentIndex, Position tail) {
    _argPos = argumentIndex;
    _tail = tail;
    if (tail == null) throw new NullInitialisationError("ArgumentPosition", "tail");
  }

  public boolean isEmpty() {
    return false;
  }

  public int queryArgumentPosition() {
    return _argPos;
  }

  public Position queryTail() {
    return _tail;
  }

  public boolean equals(Position other) {
    return other.queryArgumentPosition() == _argPos &&
           _tail.equals(other.queryTail());
  }

  public String toString() {
    return "" + _argPos + "." + _tail.toString();
  }
}

