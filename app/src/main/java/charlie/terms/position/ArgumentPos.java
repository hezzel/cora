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

import charlie.exceptions.NullStorageException;

public record ArgumentPos(int index, Position tail) implements Position {
  public ArgumentPos(int index, Position tail) {
    if (index <= 0) {
      throw new IllegalArgumentException("ArgumentPos::constructor -- given index ≤ 0");
    }
    if (tail == null) {
      throw new NullStorageException("ArgumentPos", "tail");
    }
    this.index = index;
    this.tail = tail;
  }

  public String toString() {
    return "" + index + "." + tail.toString();
  }

  public boolean equals(Position other) {
    switch (other) {
      case ArgumentPos(int id, Position tl): return index == id && tail.equals(tl);
      default: return false;
    }
  }

  public int hashCode() {
    // we choose 7 because it creates distinct hashcodes for most use cases: terms don't typically
    // have more than 6 arguments (and multiplication by 7 can be done through a bitshift)
    return 7 * tail.hashCode() + index;
  }

  public Position append(Position p) {
    return new ArgumentPos(this.index, this.tail.append(p));
  }

  public int queryHead() {
    return index;
  }

  public Position queryTail() {
    return tail;
  }
}
