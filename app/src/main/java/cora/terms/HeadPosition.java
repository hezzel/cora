/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import cora.exceptions.IllegalArgumentError;
import cora.exceptions.NullInitialisationError;

/** 
 * A head position is a position of the form i1...in.☆k, indicating the head of an application.
 * Every position is also a head position.
 */
public class HeadPosition {
  private final Position _pos;
  private final int _chop;

  /** Convert a Position to a HeadPosition. */
  HeadPosition(Position pos) {
    _pos = pos;
    _chop = 0;
    if (pos == null) throw new NullInitialisationError("HeadPosition", "pos");
  }

  /** Creates the head position pos.☆k. */
  HeadPosition(Position pos, int k) {
    _pos = pos;
    _chop = k;
    if (pos == null) throw new NullInitialisationError("HeadPosition", "pos");
    if (k < 0) throw new IllegalArgumentError("HeadPosition", "constructor",
      "Trying to create a HeadPosition with chop count < 0");
  }

  /** Returns the position pos such that this is pos.☆k */
  public Position queryPosition() {
    return _pos;
  }

  /** Returns the number of arguments to be chopped off to reach the head. */
  public int queryChopCount() {
    return _chop;
  }

  /** Returns whether this is a head position of the form ☆k, so not in a subterm. */
  public boolean isEnd() {
    return _pos.isEmpty();
  }

  /** Returns whether this is a product position. */
  public boolean isTuple() { return _pos.isTuple(); }

  /** Returns whether this is a head position of the form i.tail with i ≥ 1. */
  public boolean isArgument() {
    return _pos.isArgument();
  }

  /** Returns whether this is a head position of the form 0.tail. */
  public boolean isLambda() {
    return _pos.isLambda();
  }

  /** Returns whether this is a head position of the form !i.tail with i ≥ 1. */
  public boolean isMeta() {
    return _pos.isMeta();
  }

  /** Retuns whether this head position is actually a position (so nothing is chopped). */
  public boolean isPosition() {
    return _chop == 0;
  }

  /**
   * If the head position is in a subterm of argument si of an application h(s1,...,sn), this
   * function returns the index i of the relevant argument (1..n); otherwise it throws an
   * InappropriatePatternDataError.
   */
  public int queryArgumentPosition() {
    return _pos.queryArgumentPosition();
  }

  /**
   * If the head position is in a subterm of argument si of a meta-application Z[s1,...,sk], this
   * function returns the index i of the relevant argument (1..k); otherwise it throws an
   * InappropriatePatternDataError.
   */
  public int queryMetaPosition() {
    return _pos.queryMetaPosition();
  }

  /**
   * If the head position is in a subterm of some argument t, this function returns the position of
   * the relevant subterm in t; otherwise it throws an InappropriatePatternDataError.
   */
  public HeadPosition queryTail() {
    return new HeadPosition(_pos.queryTail(), _chop);
  }

  /** Returns whether this position and other represent the same location in a term. */
  public boolean equals(HeadPosition other) {
    return _chop == other.queryChopCount() &&
           _pos.equals(other.queryPosition());
  }

  /** Gives a suitable string representation for the HeadPosition. */
  public String toString() {
    if (_chop == 0) return _pos.toString();
    return _pos.toString().replace("ε", "☆" + _chop);
  }
}
