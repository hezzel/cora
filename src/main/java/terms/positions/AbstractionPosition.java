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
 * An AbstractionPosition is a position of the form 1.pos, and is meant to correspond only to
 * position pos in the subterm s of λx.s.
 */
public class AbstractionPosition implements Position {
  private Position _tail;

  public AbstractionPosition(Position tail) {
    _tail = tail;
    if (tail == null) throw new NullInitialisationError("AbstractionPosition", "tail");
  }

  public boolean isEmpty() {
    return false;
  }

  public int queryArgumentPosition() {
    return 1;
  }

  public Position queryTail() {
    return _tail;
  }

  public boolean equals(Position other) {
    return other.queryArgumentPosition() == 1 && _tail.equals(other.queryTail());
  }

  public String toString() {
    return "1." + _tail.toString();
  }
}

