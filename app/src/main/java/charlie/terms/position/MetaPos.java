/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms.position;

import charlie.exceptions.IllegalArgumentError;
import charlie.exceptions.NullInitialisationError;

public record MetaPos(int index, Position tail) implements Position {
  public MetaPos(int index, Position tail) {
    if (index <= 0) {
      throw new IllegalArgumentError("MetaPos", "constructor", "given index ≤ 0");
    }
    if (tail == null) {
      throw new NullInitialisationError("MetaPos", "tail");
    }
    this.index = index;
    this.tail = tail;
  }

  public String toString() {
    return "!" + index + "." + tail.toString();
  }

  public boolean equals(Position other) {
    switch (other) {
      case MetaPos(int id, Position tl): return index == id && tail.equals(tl);
      default: return false;
    }
  }

  public Position append(Position p) {
    return new MetaPos(this.index, this.tail.append(p));
  }

  public int queryHead() {
    return - index;
  }

  public Position queryTail() {
    return tail;
  }
}
