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

import charlie.exceptions.NullInitialisationError;

public record LambdaPos(Position tail) implements Position {
  public LambdaPos(Position tail) {
    if (tail == null) {
      throw new NullInitialisationError("LambdaPos", "tail");
    }
    this.tail = tail;
  }

  public String toString() {
    return "0." + tail.toString();
  }

  public boolean equals(Position other) {
    switch (other) {
      case LambdaPos(Position tl): return tail.equals(tl);
      default: return false;
    }
  }

  public Position append(Position p) {
    return new LambdaPos(this.tail.append(p));
  }

  public int queryHead() {
    return 0;
  }

  public Position queryTail() {
    return tail;
  }
}
