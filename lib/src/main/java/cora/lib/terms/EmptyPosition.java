/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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

import cora.lib.exceptions.InappropriatePatternDataError;

/** The empty position is used to indicate the current location in a term. */
class EmptyPosition implements Position {
  /** This should only be created through the PositionFactory, or EmptyPath. */
  EmptyPosition() { }

  public boolean isEmpty() {
    return true;
  }

  public boolean isArgument() {
    return false;
  }

  public boolean isLambda() {
    return false;
  }

  public int queryArgumentPosition() {
    throw new InappropriatePatternDataError("EmptyPosition", "queryArgumentPosition",
      "positions of the form i.tail with i > 0");
  }

  public Position queryTail() {
    throw new InappropriatePatternDataError("EmptyPosition", "queryTail",
      "positions of the form i.tail with");
  }

  public boolean equals(Position other) {
    return other.isEmpty();
  }

  public String toString() {
    return "ε";
  }
}

