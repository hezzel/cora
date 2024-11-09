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

public final class Geq0 extends Comparison {
  Geq0(IntegerExpression expr) { super(expr); }
  Geq0(IntegerExpression left, IntegerExpression right) { super(left, right); }
  public Geq0 negate() { return new Geq0(_expr.negate().add(-1)); }
  protected boolean evaluate(int num) { return num >= 0; }
  protected String symbol() { return ">="; }
  public int hashCode() { return 17 * _expr.hashCode() + 4; }
}

