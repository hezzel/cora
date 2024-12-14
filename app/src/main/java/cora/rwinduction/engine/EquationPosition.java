/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine;

import charlie.terms.position.Position;
import charlie.terms.position.FinalPos;

/** A position in an equation is just the combination of a side (left/right) and a position. */
public class EquationPosition {
  public enum Side { Left, Right };

  private Side _side;
  private Position _position;

  public EquationPosition(Side side, Position pos) {
    _side = side;
    _position = pos;
  }

  public EquationPosition(Side side) {
    _side = side;
    _position = new FinalPos(0);
  }

  public Side querySide() {
    return _side;
  }

  public Position queryPosition() {
    return _position;
  }

  public String toString() {
    return _side.toString() + "." + _position.toString();
  }
}

