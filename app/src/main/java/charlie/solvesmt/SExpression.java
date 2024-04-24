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

package charlie.solvesmt;

import java.util.List;

/**
 * This is a sealed class collecting an EXTREMELY LIMITED subset of the SMTLIB language.
 * It is very possible that more options will be added in the future, so treat with caution.
 */
public sealed interface SExpression {
  public record Numeral(int num) implements SExpression {
    public String toString() { return "" + num; }
  }
  public record Symbol(String name) implements SExpression {
    public String toString() { return name; }
  }
  public record SExpList(List<SExpression> lst) implements SExpression {
    public String toString() { return lst.toString(); }
  }
}

