/**************************************************************************************************
 Copyright 2019, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.lib.terms;

import cora.lib.exceptions.IllegalArgumentError;
import cora.lib.exceptions.InappropriatePatternDataError;
import cora.lib.exceptions.NullInitialisationError;

/**
 * A ConsPosition is a position of the form i.pos, where i can take any of the permitted forms
 * (currently only an integer ≥ 1).
 */
class ConsPosition implements Position {
  private int _argPos;
  private Position _tail;

  /** Default because it should only be created through the position factory. */
  ConsPosition(int argumentIndex, Position tail) {
    _argPos = argumentIndex;
    _tail = tail;
    if (tail == null) throw new NullInitialisationError("ArgumentPosition", "tail");
    if (_argPos < 0) throw new IllegalArgumentError("ConsPosition", "constructor",
      "Trying to create a position with an index < 0.");
  }

  public boolean isEmpty() {
    return false;
  }

  public boolean isArgument() {
    return _argPos > 0;
  }

  public boolean isLambda() {
    return _argPos == 0;
  }

  public int queryArgumentPosition() {
    if (_argPos == 0) throw new InappropriatePatternDataError("ConsPosition for λ",
      "queryArgumentPosition", "ConsPosition for argument positions");
    return _argPos;
  }

  public Position queryTail() {
    return _tail;
  }

  public boolean equals(Position other) {
    if (_argPos > 0) {
      return other.isArgument() &&
             other.queryArgumentPosition() == _argPos &&
             _tail.equals(other.queryTail());
    }
    else {
      return other.isLambda() && _tail.equals(other.queryTail());
    }
  }

  public String toString() {
    return "" + _argPos + "." + _tail.toString();
  }
}

