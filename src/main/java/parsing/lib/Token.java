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

package cora.parsing.lib;

/** This class represents a single Token in an input string or file. */
public class Token {
  private ParsePosition _position;
  private String _name;
  private String _text;

  /** The EOF token is returned for the end of input. */
  public static String EOF        = "EOF";
  /** The CATCHALL token is returned when none of the user-defined tokens match, and is always a
      single character. */
  public static String CATCHALL   = "CATCHALL";
  /** The SKIP token is not a true token; rather, it is the name that you should use to indicate
      that you do NOT want a token to be generated for given regular expression.  You can have
      multiple SKIP "tokens" in the token definition list.  This is typically used for whitespace
      and single-line comments. */
  public static String SKIP       = "SKIP";
  /** Returns the token that represents end-of-file (or rather, end-of-input) */
  public static Token eofToken(ParsePosition pos) { return new Token(pos, null, null); }

  /**
   * Creates a token at the given position, with the given token name and underlying string.
   * This is deliberately default and not public: tokens are meant to be created only inside the
   * cora.parsing package.
   */
  Token(ParsePosition pos, String name, String text) {
    _position = pos;
    _name = name;
    _text = text;
    if (pos == null) _position = new ParsePosition(0);
    if (name == null) _name = EOF;
    if (text == null) _text = "";
  }

  /** Returns a description of the position in the input where this token was found. */
  public String getPosition() {
    return _position.toString();
  }

  /**
   * Returns true if the position of the current token is before the position of the given toekn.
   * Note that not all positions are comparable.
   */
  public boolean before(Token other) {
    return _position.before(other._position);
  }

  /** Returns the name of the token (e.g, IDENTIFIER, WHITESPACE, BRACKETOPEN) */
  public String getName() {
    return _name;
  }

  /** Returns the text that was matched for this token */
  public String getText() {
    return _text;
  }

  /** Returns whether or not the current token is the end-of-input token. */
  public boolean isEof() {
    return _name.equals(EOF);
  }

  /** Returns a string representation of the current token, for use in testing and debugging. */
  public String toString() {
    return _position.toString() + ": " + _text + " (" + _name + ")";
  }
}

