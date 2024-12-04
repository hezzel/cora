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

package charlie.smt;

public final class Falsehood extends Constraint {
  /** Private constructor, as Constraints should be made through the SmtFactory. */
  Falsehood() { _simplified = true; }

  public Truth negate() { return new Truth(); }

  public boolean evaluate(Valuation val) { return false; }

  public Falsehood simplify() { return this; }

  public void addToSmtString(StringBuilder builder) {
    builder.append("false");
  }

  public int compareTo(Constraint other) {
    return switch (other) {
      case Falsehood _ -> 0;
      default -> -1;
    };
  }

  public int hashCode() { return 2; }
}

