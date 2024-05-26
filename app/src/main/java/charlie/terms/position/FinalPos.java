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

import charlie.exceptions.InappropriatePatternDataException;

public record FinalPos(int chopcount) implements Position {
  public FinalPos(int chopcount) {
    if (chopcount < 0) {
      throw new IllegalArgumentException("FinalPos::constructor -- chop count < 0");
    }
    this.chopcount = chopcount;
  }

  public String toString() {
    if (chopcount == 0) return "ε";
    else return "☆" + chopcount;
  }

  public boolean equals(Position other) {
    switch (other) {
      case FinalPos(int k): return chopcount == k;
      default: return false;
    }
  }

  public Position append(Position p) {
    return p;
  }
  
  public boolean isEmpty() {
    return chopcount == 0;
  }

  public boolean isFinal() {
    return true;
  }

  public int queryChopCount() {
    return chopcount;
  }

  public int queryHead() {
    throw new InappropriatePatternDataException("FinalPos", "queryHead", "non-empty positions");
  }

  public Position queryTail() {
    throw new InappropriatePatternDataException("FinalPos", "queryTail", "non-empty positions");
  }
}
