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

import charlie.exceptions.CustomParserException;
import charlie.terms.position.Position;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.printer.PrintableObject;

/** A position in an equation is just the combination of a side (left/right) and a position. */
public class EquationPosition implements PrintableObject {
  public enum Side { Left, Right };

  public static EquationPosition TOPLEFT = new EquationPosition(Side.Left, Position.empty);
  public static EquationPosition TOPRIGHT = new EquationPosition(Side.Right, Position.empty);

  private Side _side;
  private Position _position;

  public EquationPosition(Side side, Position pos) {
    _side = side;
    _position = pos;
  }

  public EquationPosition(Side side) {
    _side = side;
    _position = Position.empty;
  }

  public Side querySide() {
    return _side;
  }

  public Position queryPosition() {
    return _position;
  }

  @Override
  public void print(Printer printer) {
    String s = switch (_side) { case Left -> "L"; case Right -> "R"; };
    if (_position.isEmpty()) printer.add(s);
    else if (_position.isFinal()) printer.add(s, ".", _position);
    else printer.add(s, _position);
  }

  /**
   * Default implementation for debugging; however, proper printing should use an Outputter or
   * Printer.
   */
  public String toString() {
    Printer printer = PrinterFactory.createPrinterNotForUserOutput();
    print(printer);
    return printer.toString();
  }

  /** Checks if both the side and the position are the same as other. */
  public boolean equals(EquationPosition other) {
    return _side.equals(other._side) && _position.equals(other._position);
  }

  @Override
  public boolean equals(Object other) {
    if (other instanceof EquationPosition pos) return equals(pos);
    return false;
  }

  /**
   * This parses the given string into an EquationPosition if possible, and if not, throws an
   * appropriate CustomParserException.
   */
  public static EquationPosition parse(String desc) throws CustomParserException {
    desc = desc.trim();
    if (desc.equals("") || desc.equals("L")) return TOPLEFT;
    if (desc.equals("R")) return TOPRIGHT;
    Side side = Side.Left;
    if (desc.charAt(0) == 'L') desc = desc.substring(1);
    else if (desc.charAt(0) == 'R') { desc = desc.substring(1); side = Side.Right; }
    Position pos = Position.parse(desc);
    return new EquationPosition(side, pos);
  }
}

