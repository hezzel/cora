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

import java.util.ArrayList;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.types.TypeFactory;
import charlie.types.Type;

public class EqualSymbolsTest extends TermTestFoundation {
  @Test
  public void testIntegerEqualityBasics() {
    CalculationSymbol s = TheoryFactory.intEqualSymbol;
    assertTrue(s.queryType().toString().equals("Int → Int → Bool"));
    assertTrue(s.queryInfixPriority() == CalculationSymbol.INFIX_COMPARISON);
    assertTrue(s.queryName().equals("="));
    assertTrue(s.toString().equals("[=]"));
    assertTrue(s.toUniqueString().equals("={Int → Int → Bool}#calc"));
    assertTrue(s.queryArity() == 2);
  }

  @Test
  public void testIntegerInequalityBasics() {
    CalculationSymbol s = TheoryFactory.intDistinctSymbol;
    assertTrue(s.queryType().toString().equals("Int → Int → Bool"));
    assertTrue(s.queryInfixPriority() == CalculationSymbol.INFIX_COMPARISON);
    assertTrue(s.queryName().equals("≠"));
    assertTrue(s.toString().equals("[≠]"));
    assertTrue(s.toUniqueString().equals("≠{Int → Int → Bool}#calc"));
    assertTrue(s.queryArity() == 2);
  }

  @Test
  public void testStringEqualityBasics() {
    CalculationSymbol s = TheoryFactory.stringEqualSymbol;
    assertTrue(s.queryType().toString().equals("String → String → Bool"));
    assertTrue(s.queryInfixPriority() == CalculationSymbol.INFIX_COMPARISON);
    assertTrue(s.queryName().equals("="));
    assertTrue(s.toString().equals("[=]"));
    assertTrue(s.toUniqueString().equals("={String → String → Bool}#calc"));
    assertTrue(s.queryArity() == 2);
  }

  @Test
  public void testStringInequalityBasics() {
    CalculationSymbol s = TheoryFactory.stringDistinctSymbol;
    assertTrue(s.queryType().toString().equals("String → String → Bool"));
    assertTrue(s.queryInfixPriority() == CalculationSymbol.INFIX_COMPARISON);
    assertTrue(s.queryName().equals("≠"));
    assertTrue(s.toString().equals("[≠]"));
    assertTrue(s.toUniqueString().equals("≠{String → String → Bool}#calc"));
    assertTrue(s.queryArity() == 2);
  }

  @Test
  public void testEquality() {
    CalculationSymbol[] symbs = { TheoryFactory.intEqualSymbol,
                                  TheoryFactory.intDistinctSymbol,
                                  TheoryFactory.stringEqualSymbol,
                                  TheoryFactory.stringDistinctSymbol };
    for (int i = 0; i < symbs.length; i++) {
      for (int j = 0; j < symbs.length; j++) {
        if (i == j) assertTrue(symbs[i].equals(symbs[j]));
        else assertFalse(symbs[i].equals(symbs[j]));
      }
    }
  }

  @Test
  public void testToString() {
    CalculationSymbol e = TheoryFactory.intEqualSymbol;
    CalculationSymbol u = TheoryFactory.intDistinctSymbol;
    CalculationSymbol a = TheoryFactory.stringEqualSymbol;
    CalculationSymbol b = TheoryFactory.stringDistinctSymbol;
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.stringSort);
    Value three = TheoryFactory.createValue(3);
    Value str = TheoryFactory.createValue("str");
    Term eterm = e.apply(x).apply(three);
    Term uterm = u.apply(three).apply(x);
    Term aterm = a.apply(z).apply(str);
    Term bterm = b.apply(str).apply(z);
    assertTrue(eterm.toString().equals("x = 3"));
    assertTrue(uterm.toString().equals("3 ≠ x"));
    assertTrue(aterm.toString().equals("z = \"str\""));
    assertTrue(bterm.toString().equals("\"str\" ≠ z"));
  }
}
