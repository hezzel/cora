/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.smt;

public final class SValue extends StringExpression {
  private String _s;

  /** The constructor is hidden, since StringExpressions should be made through the SmtFactory. */
  SValue(String txt) {
    _s = txt;
  }

  public String queryValue() {
    return _s;
  }

  public String evaluate(Valuation val) {
    return _s;
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append(encode(_s));
  }

  public static String encode(String txt) {
    StringBuilder ret = new StringBuilder("\"");
    for (int i = 0; i < txt.length(); i++) {
      char c = txt.charAt(i);
      if (c == '"') ret.append("\"\"");
      else if (32 <= c && c <= 126) ret.append(c);
      else ret.append("\\u{" + Integer.toHexString((int)c) + "}");
    }
    ret.append("\"");
    return ret.toString();
  }

  public int compareTo(StringExpression other) {
    return switch (other) {
      case SValue v -> _s.compareTo(v._s);
      default -> -1;
    };
  }

  public int hashCode() {
    return 2 * _s.hashCode();
  }
}

