/**************************************************************************************************
 Copyright 2022, 2023 Cynthia Kop

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
import cora.exceptions.CustomParserError;

public final class PositionFactory {
  //  Factories shouldn't be instantiated as objects
  private PositionFactory() { }

  public static final Position empty = new EmptyPosition();

  public static Position createArg(int index, Position tail) {
    if (index <= 0) {
      throw new IllegalArgumentError("PositionFactory", "createArg", "given index is not positive");
    }
    return new ConsPosition(index, tail);
  }

  public static Position createTuple(int index, Position tail) {
    if (index <= 0) {
      throw new IllegalArgumentError("PositionFactory", "createTuple", "index is not positive");
    }
    return new ConsPosition(index, tail);
  }

  public static Position createLambda(Position tail) {
    return new ConsPosition(0, tail);
  }

  public static Position createMeta(int index, Position tail) {
    if (index <= 0) {
      throw new IllegalArgumentError("PositionFactory","createMeta","given index is not positive");
    }
    return new ConsPosition(-index, tail);
  }

  public static HeadPosition createHead(Position pos, int chop) {
    if (chop == 0) return new HeadPosition(pos);
    else return new HeadPosition(pos, chop);
  }

  /**
   * Returns the HeadPosition that the given string represents, or throws an appropriate
   * CustomParserError if it does not represent anything.
   */
  public static HeadPosition parseHPos(String text) {
    if (text.equals("")) return new HeadPosition(empty);

    // find chop count, if any, and remove that part from the text
    int chop = 0, n;
    int star = text.indexOf('☆');
    if (star == -1) star = text.indexOf('*');
    if (star != -1) {
      try { chop = Integer.parseInt(text.substring(star+1)); }
      catch (NumberFormatException ex) {
        throw new CustomParserError(1, star + 1, text.substring(star+1),
          "head chop count should be an integer");
      }
      n = star;
    }
    else if (text.charAt(text.length()-1) == 'ε') n = text.length()-1;
    else n = text.length();
    if (n > 0 && text.charAt(n-1) == '.') n--;

    // read parts from right to left, building a position as we go
    Position ret = empty;
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
      if (meta) num = -num;
      ret = new ConsPosition(num, ret);
      n = dot;
    }

    return new HeadPosition(ret, chop);
  }

  /**
   * Returns the Position that the given string represents, or throws an appropriate parserError
   * if it does not represent anything.
   */
  public static Position parsePos(String text) {
    int c = text.indexOf('*');
    if (c == -1) c = text.indexOf('☆');
    if (c != -1) throw new CustomParserError(1, c, text,
      "a position does not contain * or ☆; only head positions do");
    HeadPosition pos = parseHPos(text);
    return pos.queryPosition();
  }
}
