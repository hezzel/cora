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

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;

import charlie.solvesmt.SExpression;

public class SmtParserTest {
  @Test
  public void testReadNumeral() {
    switch (SmtParser.readExpressionFromString("123")) {
      case SExpression.Numeral(int n): assertTrue(n == 123); break;
      default: assertTrue(false);
    }
    switch (SmtParser.readExpressionFromString("0")) {
      case SExpression.Numeral(int n): assertTrue(n == 0); break;
      default: assertTrue(false);
    }
    // this should probably give an error in the future, but for now we allow it as an identifier
    switch (SmtParser.readExpressionFromString("001")) {
      case SExpression.Symbol(String str): assertTrue(str.equals("001")); break;
      default: assertTrue(false);
    }
  }

  @Test
  public void testReadString() {
    switch (SmtParser.readExpressionFromString("\"123\"\"4a\"")) {
      case SExpression.StringConstant(String t): assertTrue(t.equals("123\"4a")); break;
      default: assertTrue(false);
    }
    switch (SmtParser.readExpressionFromString("\"\\u{48}\\u219E\"")) {
      case SExpression.StringConstant(String t): assertTrue(t.equals("H↞")); break;
      default: assertTrue(false);
    }
  }

  @Test
  public void testReadComplexExpression() {
    SExpression expr = SmtParser.readExpressionFromString("(a ((b x) 3) (c))");
    assertTrue(expr instanceof SExpression.SExpList);
    SExpression.SExpList l1 = (SExpression.SExpList)expr;
    assertTrue(l1.lst().size() == 3);
    assertTrue(l1.lst().get(0) instanceof SExpression.Symbol);
    assertTrue(l1.lst().get(1) instanceof SExpression.SExpList);
    assertTrue(l1.lst().get(2) instanceof SExpression.SExpList);

    assertTrue(l1.lst().get(0).toString().equals("a"));
    SExpression.SExpList l2 = (SExpression.SExpList)l1.lst().get(1);
    SExpression.SExpList l3 = (SExpression.SExpList)l1.lst().get(2);

    assertTrue(l2.lst().size() == 2);
    assertTrue(l2.lst().get(0) instanceof SExpression.SExpList);
    assertTrue(l2.lst().get(1) instanceof SExpression.Numeral);

    assertTrue(l3.lst().size() == 1);
    assertTrue(l3.lst().get(0) instanceof SExpression.Symbol);
    assertTrue(l3.lst().get(0).toString().equals("c"));

    SExpression.SExpList l4 = (SExpression.SExpList)l2.lst().get(0);
    assertTrue(l2.lst().get(1).toString().equals("3"));

    assertTrue(l4.lst().size() == 2);
    assertTrue(l4.lst().get(0) instanceof SExpression.Symbol);
    assertTrue(l4.lst().get(0).toString().equals("b"));
    assertTrue(l4.lst().get(1) instanceof SExpression.Symbol);
    assertTrue(l4.lst().get(1).toString().equals("x"));
  }

  @Test
  public void testReadMultipleExpressinos() {
    List<SExpression> lst = SmtParser.readExpressionsFromString("sat (= a \"test\") (= b (- 4))");
    assertTrue(lst.size() == 3);
    assertTrue(lst.get(0) instanceof SExpression.Symbol);
    assertTrue(lst.get(0).toString().equals("sat"));
    assertTrue(lst.get(1) instanceof SExpression.SExpList);
    assertTrue(lst.get(2) instanceof SExpression.SExpList);
    assertTrue(((SExpression.SExpList)lst.get(1)).lst().get(0).toString().equals("="));
    assertTrue(((SExpression.SExpList)lst.get(2)).lst().get(0).toString().equals("="));
    assertTrue(((SExpression.SExpList)lst.get(2)).lst().get(2) instanceof SExpression.SExpList);
  }
}

