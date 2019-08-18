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

/** The empty position is used to indicate the current location in a term. */
public class EmptyPosition implements Position {
  public boolean isEmpty() {
    return true;
  }

  public int queryArgumentPosition() {
    return -1;
  }

  public Position queryTail() {
    return null;
  }

  public boolean equals(Position other) {
    return other.isEmpty();
  }

  public String toString() {
    return "ε";
  }
}

