/**************************************************************************************************
 Copyright 2023--2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.theory;

import java.util.Map;
import charlie.types.Base;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.InappropriatePatternDataException;
import charlie.terms.FunctionSymbolInherit;

/**
 * StringValues are strings, which can be printed to the user when using a logically constrained
 * TRS as a kind of programming language.  Strings have an underlying string (the *actual* string)
 * and a representation with escape characters (the name).
 */
public final class StringValue extends FunctionSymbolInherit implements Value {
  private final String _value;

  private static String makePrintable(String str) {
    return "\"" + str.replace("\\", "\\\\")
                    .replace("\n", "\\n")
                    .replace("\"", "\\\"") + "\"";
  }

  /**
   * This creates a string value representing the given string.  The string is supposed to be
   * presented as is; there should not be surrounding quotes or escape sequences in there.
   */
  StringValue(String str) {
    super(makePrintable(str), TypeFactory.stringSort, Value.SPECIALNAME);
    _value = str;
  }

  /**
   * This returns the actual string representing this term, for instance including newlines, not
   * its printable version where newlines are replaced with \n (the printable version is its name).
   */
  public String getString() {
    return _value;
  }

  /** @return the string sort */
  @Override
  public final Base queryType() { return TypeFactory.stringSort; }

  /** Helper constructor for parseUserStringValue */
  private StringValue(String str, String escaped) {
    super(escaped, TypeFactory.stringSort, Value.SPECIALNAME);
    _value = str;
  }

  /**
   * This function takes a string as supplied by a programmer -- with quotes and potentially
   * escape characters -- and parses it into a string value
   */
  static StringValue parseUserStringValue(String str) throws IncorrectStringException {
    if (str.length() < 2 || str.charAt(0) != '"' || str.charAt(str.length()-1) != '"') {
      throw new IncorrectStringException(str, "string should have double quotes on either side");
    }
    StringBuilder ret = new StringBuilder();
    for (int i = 1; i < str.length()-1; i++) {
      if (str.charAt(i) != '\\') ret.append(str.substring(i, i+1));
      else {
        if (str.charAt(i+1) == 'n') ret.append("\n");
        else if (str.charAt(i+1) == '\\') ret.append("\\");
        else if (str.charAt(i+1) == '"') ret.append("\"");
        else throw new IncorrectStringException(str, "stray escape character at position " +
          (i+1) + ": " + str.substring(i, i+2) + " is not an escape sequence.");
        i++;
      }
    }
    return new StringValue(ret.toString(), str);
  }

  @Override
  public int hashCode(Map mu) { return _value.hashCode(); }

  /** @return false, since nullary constants cannot be infix */
  @Override
  public boolean isInfixSymbol() { return false; }

  /** @return this, since a value is not polymorphic, so substituting has no effect */
  public StringValue substituteType(Type.ISubstitution typeMapping) { return this; }
}
