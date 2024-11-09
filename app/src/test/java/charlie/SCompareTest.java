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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;

/** Testing the two string comparison constraints */
public class SCompareTest {
  @Test
  public void testBasics() {
    StringExpression expr = new SValue("abcd");
    SVar x = new SVar(3);
    EqS e = new EqS(expr, x);
    UneqS u = new UneqS(x, expr);
    assertTrue(e.queryLeft() == x);
    assertTrue(u.queryLeft() == x);
    assertTrue(e.queryRight() == expr);
    assertTrue(u.queryRight() == expr);
    assertTrue(e.negate().equals(u));
    assertTrue(u.negate().equals(e));
    assertFalse(e.equals(u));
    assertFalse(u.equals(e));
    assertTrue(u.hashCode() == e.hashCode() + 1);
    assertTrue(e.toString().equals("s3 = \"abcd\""));
    assertTrue(u.toString().equals("s3 # \"abcd\""));
    assertTrue(e.toSmtString().equals("(= s3 \"abcd\")"));
    assertTrue(u.toSmtString().equals("(distinct s3 \"abcd\")"));
  }
}
