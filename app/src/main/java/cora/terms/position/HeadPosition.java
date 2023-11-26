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

package cora.terms.position;

import cora.exceptions.CustomParserError;
import cora.exceptions.IllegalArgumentError;
import cora.exceptions.NullInitialisationError;

/** 
 * A head position is a position of the form i1...in.☆k, indicating the head of an application,
 * where k items are chopped off the right.  Every position is also a head position of the form
 * i1...in.☆0.
 */
public record HeadPosition(Position pos, int chop) {
  /** Creates a position pos☆chop */
  public HeadPosition(Position pos, int chop) {
    this.pos = pos;
    this.chop = chop;
    if (pos == null) throw new NullInitialisationError("HeadPosition", "pos");
    if (chop < 0) throw new IllegalArgumentError("HeadPosition", "constructor",
      "Trying to create a HeadPosition with chop count < 0");
  }

  /** Creates a position pos☆0, so a head position directly corresponding to the given position */
  public HeadPosition(Position pos) {
    this(pos, 0);
  }

  /** Returns the position pos such that this is pos.☆k */
  public Position queryPosition() {
    return pos;
  }

  /** Returns the number of arguments to be chopped off to reach the head. */
  public int queryChopCount() {
    return chop;
  }

  /** Returns whether this head position and other represent the same location in a term. */
  public boolean equals(HeadPosition other) {
    return chop == other.queryChopCount() &&
           pos.equals(other.queryPosition());
  }

  /** Gives a suitable string representation for the HeadPosition. */
  public String toString() {
    if (chop == 0) return pos.toString();
    return pos.toString().replace("ε", "☆" + chop);
  }

  /**
   * Returns the HeadPosition that the given string represents, or throws an appropriate
   * CustomParserError if it does not represent anything.
   */
  public static HeadPosition parse(String text) {
    // find chop count, if any, and remove that part from the text
    int chp = 0;
    int star = text.indexOf('☆');
    if (star == -1) star = text.indexOf('*');
    if (star != -1) {
      try { chp = Integer.parseInt(text.substring(star+1)); }
      catch (NumberFormatException ex) {
        throw new CustomParserError(1, star + 1, text.substring(star+1),
          "head chp count should be an integer");
      }
      text = text.substring(0, star);
    }
    return new HeadPosition(Position.parse(text), chp);
  }
}
