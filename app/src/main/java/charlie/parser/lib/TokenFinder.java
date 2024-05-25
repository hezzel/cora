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

package charlie.parser.lib;

import java.util.regex.Pattern;
import java.util.regex.Matcher;

/**
 * The TokenFinder keeps track of a number of regular expressions, each of which defines a token to
 * be used for parsing.  In addition, it can be used to check if a string starts with one of these
 * expressions, and if so, generate a Token accordingly.
 */
class TokenFinder {
  /** This class contains the information for all defined tokens */
  private class PatternInfo {
    String _name;       // the name of the token
    Pattern _pattern;   // the regular expression defining the token
    PatternInfo(String name, String regexp) { _name = name; _pattern = Pattern.compile(regexp); }
  }

  /** The tokens we use for parsing the input. */
  private PatternInfo[] _patterns;

  /**
   * Generate a TokenFinder which keeps track of the regular expression/token pairs defined by the
   * given array.  This array is expected to have a form
   * "regexp", "token name", "regexp", "token name", ...
   * Each token name is expected to consist only of capitalised letters and underscores.  The same
   * name may occur multiple times; the regexp should be unique (if not, only the first will be
   * used).
   */
  TokenFinder(String[] tokens) {
    _patterns = new PatternInfo[tokens.length/2+1];

    if (tokens.length%2 == 1) {
      throw new IllegalArgumentException("TokenFinder: " +
        "given a Token array wich an odd number of elements!");
    }
    
    for (int i = 0; i < tokens.length; i += 2) {
      String name = tokens[i+1];
      if (name.equals(Token.EOF) || name.equals(Token.CATCHALL)) {
        throw new IllegalArgumentException("TokenFinder: " +
          "Token array tries to define the " + name + " token (this name is reserved).");
      }
      for (int j = 0; j < name.length(); j++) {
        char c = name.charAt(j);
        if (c != '_' && (c < 'A' || c > 'Z')) {
          // do this to catch it when users mix up the token name and expression
          throw new IllegalArgumentException("TokenFinder: " +
            "Illegal token: " + name + "!  Token names should consist only of capital letters " +
            "and underscores.");
        }
      }
       _patterns[i/2] = new PatternInfo(tokens[i+1], tokens[i]);
    }
    _patterns[tokens.length/2] = new PatternInfo(Token.CATCHALL, ".|\\R");
  }

  /**
   * This function finds the longest string s such that txt[start..] can be written as s t and
   * there is a token pattern that matches s.  It returns the token for this pattern, set up with
   * the given position for use in error messages, and the text s.
   *
   * Note that tokens are expected to be non-empty; hence, if txt is the empty string or start ≥
   * its length, then null is returned instead.  For non-empty strings, there is always a
   * matching token: if all else fails, the CATCHALL token will be returned, with the first
   * character of txt.
   */
  Token matchStart(String txt, int start, ParsePosition pos) {
    int bestsofar = 0;
    Token token = null;
    if (start < 0) throw new Error("matchStart called with negative start");
    if (start >= txt.length()) return token;
    if (pos == null) pos = new ParsePosition(start + 1);
    for (int i = 0; i < _patterns.length; i++) {
      Matcher matcher = _patterns[i]._pattern.matcher(txt);
      matcher.useAnchoringBounds(false);
      matcher.region(start, txt.length());
      if (matcher.lookingAt()) {
        int len = matcher.end();
        if (len > bestsofar) {
          bestsofar = len;
          token = new Token(pos, _patterns[i]._name, matcher.group());
          if (len == txt.length()) return token;
        }
      }
    }
    // catch characters not captured by . if any remain, just in case
    if (token == null) token = new Token(pos, Token.CATCHALL, txt.substring(0,1));
    return token;
  }
}
