/**************************************************************************************************
 Copyright 2019, 2020 Cynthia Kop

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
import cora.interfaces.terms.Term;
import cora.exceptions.NullInitialisationError;

/**
 * A SubPosition is a position that is not empty, which can occur in any kind of term.
 * In traditional definition (where a position is just a sequence of numbers), this is a position
 * of the form i p.
 */
public class SubPosition implements Position {
  private int _kind;      // 1: functional term; 2: varterm; 3: abstraction
  private int _argPos;    // the index i
  private Position _tail; // the rest p of the position

  /** Create a SubPosition that addresses a subterm in the given term. */
  public SubPosition(int argumentIndex, Position tail, Term term) {
    if (tail == null) throw new NullInitialisationError("SubPosition", "tail");
    if (term == null) throw new NullInitialisationError("SubPosition", "term");
    _argPos = argumentIndex;
    _tail = tail;
    _kind = 0;
    if (term.isFunctionalTerm()) _kind = 1;
    else if (term.isVarTerm()) _kind = 2;
    else if (term.isAbstraction()) _kind = 3;
  }

  /** Private constructor to support the static factory functions. */
  private SubPosition(int argumentIndex, Position tail, int kind) {
    _argPos = argumentIndex;
    _tail = tail;
    _kind = kind;
    if (tail == null) throw new NullInitialisationError("SubPosition", "tail");
  }

  /** This returns a position argument * tail, marked as a position in a functional term. */
  public static SubPosition makeFunctionalPos(int argument, Position tail) {
    return new SubPosition(argument, tail, 1);
  }

  /** This returns a position argument * tail, marked as a position in a varterm. */
  public static SubPosition makeVartermPos(int argument, Position tail) {
    return new SubPosition(argument, tail, 2);
  }

  /** This returns a position 1 * tail, marked as a position in an abstraction. */
  public static SubPosition makeAbstractionPos(Position tail) {
    return new SubPosition(1, tail, 3);
  }

  public boolean isEmpty() {
    return false;
  }
  
  public boolean isAbstractionPosition() {
    return _kind == 3;
  }

  public boolean isFunctionalPosition() {
    return _kind == 1;
  }

  public boolean isVartermPosition() {
    return _kind == 2;
  }

  public int queryArgumentPosition() {
    return _argPos;
  }

  public Position queryTail() {
    return _tail;
  }

  public boolean equals(Position other) {
    if (other.isEmpty()) return false;
    if (_kind == 1) return other.isFunctionalPosition();
    if (_kind == 2) return other.isVartermPosition();
    if (_kind == 3) return other.isAbstractionPosition();
    return true;
  }

  public String toString() {
    return "" + _argPos + "." + _tail.toString();
  }
}

