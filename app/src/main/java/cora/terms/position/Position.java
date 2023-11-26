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

/**
 * A position indicates a location in a term, which has one of the following shapes:
 * <p><ul>
 *  <li> ε, which refers to the current term
 *  <li> [index] tail, where the term is h(s1,...,sn) or ⦅s1,..., sn⦆, index ∈ {1..n}, and tail a
 *  position in s_index
 *  <li> [0] tail, where the term is λx.s or (λx.s)(t1,...,tn)  and tail a position in s
 *  <li> ![index] tail, where the term is Z[s1,...,sk] or Z[s1,...,sk](t1,...,tn), index
 *  ∈ {1..k}, and tail a position in s_index.
 *  So this does NOT include head positions.
 *  </ul></p>
 * <p>
 * A Position can be used to find (and possibly replace) the subterm at that position.
 * <b>Note:</b> all instances of Position must (and can be expected to) be immutable.
 * </p>
 */

public sealed interface Position permits
  EmptyPos, ArgumentPos, LambdaPos, MetaPos {

  /** Returns whether this position and other represent the same location in a term. */
  boolean equals(Position other);

  /** Gives a unique string representation for the position. */
  String toString();

  /** Access function: reads a position from string. */
  public static Position parse(String text) {
    if (text.equals("")) return new EmptyPos();
    // give the right error message if the input is a head position rather than a position
    int n = text.lastIndexOf('*');
    if (n < 0) n = text.lastIndexOf('☆');
    if (n > 0) {
      throw new CustomParserError(1, n + 1, text, "stars should only occur in head positions");
    }
    // find point where the interesting part of the position ends
    if (text.charAt(text.length()-1) == 'ε') n = text.length()-1;
    else n = text.length();
    if (n > 0 && text.charAt(n-1) == '.') n--;
    // read parts from right to left, building a position as we go
    Position ret = new EmptyPos();
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
        throw new CustomParserError(1, dot+1, part, "position index should be at least 0");
      }
      if (meta) ret = new MetaPos(num, ret);
      else if (num == 0) ret = new LambdaPos(ret);
      else ret = new ArgumentPos(num, ret);
      n = dot;
    }
    return ret;
  }
}

