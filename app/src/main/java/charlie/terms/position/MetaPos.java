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

package charlie.terms.position;

import charlie.util.NullStorageException;

public record MetaPos(int index, Position tail) implements Position {
  public MetaPos(int index, Position tail) {
    if (index <= 0) {
      throw new IllegalArgumentException("MetaPos::constructor -- given index ≤ 0");
    }
    if (tail == null) {
      throw new NullStorageException("MetaPos", "tail");
    }
    this.index = index;
    this.tail = tail;
  }

  public String toString() { return toStringDefault(); }

  public boolean equals(Position other) {
    switch (other) {
      case MetaPos(int id, Position tl): return index == id && tail.equals(tl);
      default: return false;
    }
  }

  public boolean equals(Object other) {
    if (other instanceof Position p) return equals(p);
    return false;
  }

  public int hashCode() {
    return 7 * tail.hashCode() + index;
    // this is the same as for ArgumentPos, but that's okay -- we would not typically have both
    // i.p and !i.p in the same function, as they cannot be positions of the same term
  }

  public Position append(Position p) {
    return new MetaPos(this.index, this.tail.append(p));
  }

  public int queryChopCount() {
    return tail.queryChopCount();
  }

  public int compareTo(Position pos) {
    if (pos.isFinal()) return 1;
    int c = this.queryHead() - pos.queryHead();
    if (c != 0) return c;
    return this.tail.compareTo(pos.queryTail());
  }

  public int queryHead() {
    return - index;
  }

  public Position queryTail() {
    return tail;
  }
}
