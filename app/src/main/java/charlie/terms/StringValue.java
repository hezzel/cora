/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import java.util.Map;
import charlie.types.TypeFactory;

/**
 * StringValues are strings, which can be printed to the user when using a logically constrained
 * TRS as a kind of proramming language.
 */
class StringValue extends ValueInherit {
  private final String _value;
  private final String _escapedValue;

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
    super(TypeFactory.stringSort);
    _value = str;
    _escapedValue = makePrintable(str);
  }

  /** Helper constructor for parseUserStringValue */
  private StringValue(String str, String escaped) {
    super(TypeFactory.stringSort);
    _value = str;
    _escapedValue = escaped;
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

  /** Returns the escaped string representation (with quotes) of this string. */
  public String queryName() {
    return _escapedValue;
  }

  /** Returns the standard string representation of the symbol. */
  public String toUniqueString() {
    return _escapedValue;
  }

  public boolean equals(FunctionSymbol symbol) {
    if (symbol == null) return false;
    if (!symbol.isValue()) return false;
    if (!symbol.queryType().equals(TypeFactory.stringSort)) return false;
    return symbol.toValue().queryName().equals(_escapedValue);
  }

  public int hashCode(Map<Variable,Integer> mu) {
    return _value.hashCode();
  }

  public int getInt() {
    throw new InappropriatePatternDataException("StringValue", "getInt", "integer values");
  }

  public String getString() {
    return _value;
  }

  public boolean getBool() {
    throw new InappropriatePatternDataException("StringValue", "getBool", "boolean values");
  }
}
