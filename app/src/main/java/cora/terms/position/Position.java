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

package cora.terms.position;

import cora.exceptions.CustomParserError;
import cora.exceptions.InappropriatePatternDataError;

/**
 * Positions are a tool to refer to a specific location in a term.
 *
 * Inherently, a Position is nothing more than a sequence that has one of two forms:
 * <p><ul>
 *   <li> [item_1].[item_2]...[item_n].ε (called a full position)
 *   <li> [item_1].[item_2]...[item_n].☆k with k > 0 (called a partial position)
 * </ul></p>
 * where each item [item_i] is an integer.  Negative integers are denoted !i instead of -i in
 * printing and parsing.
 *
 * Positions are implemented essentially as a list, meaning a Position has one of the following
 * shapes:
 * <p><ul>
 *  <li> ε or ☆k with k > 0 (final positions); we say that ε is the empty position
 *  <li> i.p; we refer to i as the head and to p as the tail
 *  </ul></p>
 * <p>
 *
 * Positions gain their meaning in the context of terms: for a given term, certain positions refer
 * to specific subterms (and not all positions refer to a subterm)!  Specifically:
 * <p><ul>
 *   <li> for a term h(s1,...,sn), i.p refers ro the subterm at position p in si if 0 < i ≤ n
 *   <li> for a term λx.t or (λx.t)(s1,...,sn), 0.p refers to the subterm at position p in t
 *   <li> for a term Z⟨t1,...,tk⟩(s1,...,sn), !i.p refers to the subterm at position p in ti if
 *     0 < i ≤ k
 *   <li> for any term s, ε refers to s itself
 *   <li> for a term h(s{1},...,s{n}), ☆k refers to h(s{1},...,s{n-k})
 * </ul></p>
 *
 * <b>Note:</b> all instances of Position must (and can be expected to) be immutable.
 */

public sealed interface Position permits
  FinalPos, ArgumentPos, LambdaPos, MetaPos {

  /** Returns whether this position and other are the same list. */
  boolean equals(Position other);

  /** Gives a unique string representation for the position. */
  String toString();

  /** Returns whether this is the empty position or not. */
  default boolean isEmpty() { return false; }

  /** Returns whether this is a final position (so ε or ☆k). */
  default boolean isFinal() { return false; }

  /**
   * If the current Position is a partial position of the form ☆k, this returns k; if it is an
   * empty position ε it returns 0.  If it is not a final position, this instead throws an
   * InappropriatePatternDataError.
   */
  default int queryChopCount() {
    throw new InappropriatePatternDataError("Position", "queryChopCount", "final positions");
  }

  /**
   * For a position x.tail, returns x (returning -i for a meta-position !i).
   * For a final position, this throws an InappropriatePatternDataError.
   */
  int queryHead();

  /**
   * For a position x.tail, returns tail.
   * For a final position, this throws an InappropriatePatternDataError.
   */
  Position queryTail();

  /** Stores a cached version of the empty position for convenient reuse. */
  public static final Position empty = new FinalPos(0);

  /**
   * Access function: reads a position from string. 
   * Positions are strings of integers, separated by periods, and possibly ending in .ε (for a
   * full position), or .☆k with k > 0 (for a partial position).  If omitted, the ending .ε is
   * assumed.  Instead of supplying a negative number, also !i with i > 0 may be used.
   */
  public static Position parse(String text) {
    if (text.equals("")) return empty;

    // find chop count, if any, and remove that part from the text
    int chp = 0, n;
    int star = text.indexOf('☆');
    if (star == -1) star = text.indexOf('*');
    if (star != -1) {
      try { chp = Integer.parseInt(text.substring(star+1)); }
      catch (NumberFormatException ex) {
        throw new CustomParserError(1, star + 1, text.substring(star+1),
          "chop count should be an integer");
      }
      n = star;
    }
    else if (text.charAt(text.length()-1) == 'ε') n = text.length()-1;
    else n = text.length();
    if (n > 0 && text.charAt(n-1) == '.') n--;

    // read parts from right to left, building a position as we go
    Position ret = chp == 0 ? empty : new FinalPos(chp);
    while (n > 0) {
      int dot = text.lastIndexOf('.', n-1);
      if (dot == n-1) throw new CustomParserError(1, dot+1, text, "empty position index");
      String part = text.substring(dot+1, n);
      boolean meta = false;
      if (part.length() > 0 && part.charAt(0) == '!') {
        meta = true;
        part = part.substring(1);
      }
      int num;
      try { num = Integer.parseInt(part); }
      catch (NumberFormatException ex) {
        throw new CustomParserError(1, dot+1, part, "position index should be an integer");
      }
      if (num < 0) {
        meta = true;
        num = -num;
      }
      if (meta) ret = new MetaPos(num, ret);
      else if (num == 0) ret = new LambdaPos(ret);
      else ret = new ArgumentPos(num, ret);
      n = dot;
    }

    return ret;
  }
}

