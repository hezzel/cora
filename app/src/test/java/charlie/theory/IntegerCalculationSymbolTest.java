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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import charlie.types.TypeFactory;
import charlie.types.Type;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;

public class IntegerCalculationSymbolTest {
  @Test
  public void testPlusBasics() {
    CalculationSymbol p = TheoryFactory.plusSymbol;
    assertTrue(p.queryType().toString().equals("Int → Int → Int"));
    assertTrue(p.queryInfixPriority() == CalculationSymbol.INFIX_PLUS);
    assertTrue(p.queryName().equals("+"));
    assertTrue(p.toString().equals("[+]"));
    assertTrue(p.querySpecial().equals("calc"));
    assertTrue(p.queryArity() == 2);
  }

  public void testMinusBasics() {
    CalculationSymbol p = TheoryFactory.minusSymbol;
    assertTrue(p.queryType().toString().equals("Int → Int → Int"));
    assertTrue(p.queryInfixPriority() == CalculationSymbol.INFIX_PLUS);
    assertTrue(p.queryName().equals("-"));
    assertTrue(p.toString().equals("[-]"));
    assertTrue(p.queryArity() == 2);
  }

  @Test
  public void testTimesBasics() {
    CalculationSymbol t = TheoryFactory.timesSymbol;
    assertTrue(t.queryType().toString().equals("Int → Int → Int"));
    assertTrue(t.queryInfixPriority() == CalculationSymbol.INFIX_TIMES);
    assertTrue(t.queryName().equals("*"));
    assertTrue(t.toString().equals("[*]"));
    assertTrue(t.queryArity() == 2);
  }

  @Test
  public void testNegateBasics() {
    CalculationSymbol m = TheoryFactory.negateSymbol;
    assertTrue(m.queryType().toString().equals("Int → Int"));
    assertTrue(m.queryInfixPriority() == CalculationSymbol.INFIX_UNARY);
    assertTrue(m.queryName().equals("~"));
    assertTrue(m.toString().equals("[~]"));
    assertTrue(m.queryArity() == 1);
  }

  @Test
  public void testDivBasics() {
    CalculationSymbol p = TheoryFactory.divSymbol;
    assertTrue(p.queryType().toString().equals("Int → Int → Int"));
    assertTrue(p.queryInfixPriority() == CalculationSymbol.INFIX_DIVMOD);
    assertTrue(p.queryName().equals("/"));
    assertTrue(p.toString().equals("[/]"));
    assertTrue(p.queryArity() == 2);
  }

  @Test
  public void testModBasics() {
    CalculationSymbol p = TheoryFactory.modSymbol;
    assertTrue(p.queryType().toString().equals("Int → Int → Int"));
    assertTrue(p.queryInfixPriority() == CalculationSymbol.INFIX_DIVMOD);
    assertTrue(p.queryName().equals("%"));
    assertTrue(p.toString().equals("[%]"));
    assertTrue(p.queryArity() == 2);
  }

  @Test
  public void testSimplePlusToString() {
    CalculationSymbol f = TheoryFactory.plusSymbol;
    assertTrue(f.toString().equals("[+]"));
    Value v = new IntegerValue(3);
    assertTrue(f.apply(v).toString().equals("[+](3)"));
    Value w = new IntegerValue(13);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(v);
    args.add(w);
    assertTrue(f.apply(args).toString().equals("3 + 13"));
  }

  @Test
  public void testSimpleTimesToString() {
    CalculationSymbol f = TheoryFactory.timesSymbol;
    assertTrue(f.toString().equals("[*]"));
    Value v = new IntegerValue(3);
    assertTrue(f.apply(v).toString().equals("[*](3)"));
    Value w = new IntegerValue(13);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(v);
    args.add(w);
    assertTrue(f.apply(args).toString().equals("3 * 13"));
  }

  @Test
  public void testSimpleNegateToString() {
    CalculationSymbol f = TheoryFactory.negateSymbol;
    assertTrue(f.toString().equals("[~]"));
    Value v = new IntegerValue(3);
    assertTrue(f.apply(v).toString().equals("~(3)"));
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    assertTrue(f.apply(x).toString().equals("~(x)"));
  }

  @Test
  public void testMinusWithNegativeValue() {
    CalculationSymbol f = TheoryFactory.minusSymbol;
    assertTrue(f.toString().equals("[-]"));
    Value v = new IntegerValue(-3);
    assertTrue(f.apply(v).toString().equals("[-](-3)"));
  }

  @Test
  public void testMinusWithComplexArgument() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Term s = TheoryFactory.minusSymbol.apply(TheoryFactory.plusSymbol.apply(x).apply(y));
    assertTrue(s.toString().equals("[-](x + y)"));
    s = TheoryFactory.negateSymbol.apply(TheoryFactory.timesSymbol.apply(x).apply(y));
    assertTrue(s.toString().equals("~(x * y)"));
  }

  @Test
  public void testPrintPlusNegativeValue() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term s = TermFactory.createApp(TheoryFactory.plusSymbol, x, new IntegerValue(-3));
    assertTrue(s.toString().equals("x + -3"));
  }

  @Test
  public void testPrintMinus() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    CalculationSymbol p = TheoryFactory.plusSymbol;
    Term s = TermFactory.createApp(TheoryFactory.minusSymbol, x, TermFactory.createApp(p, y, z));
    assertTrue(s.toString().equals("x - (y + z)"));
  }

  @Test
  public void testPrintMinusMultiplication() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    Term s = TermFactory.createApp(TheoryFactory.minusSymbol, x,
      TermFactory.createApp(TheoryFactory.timesSymbol, y, z));
    assertTrue(s.toString().equals("x - y * z"));
  }

  @Test
  public void testPlusLeftAssociativity() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    Term s = TermFactory.createApp(plus, TermFactory.createApp(plus, x, y), z);
    assertTrue(s.toString().equals("x + y + z"));
  }

  @Test
  public void testPlusNotRightAssociative() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    Term s = TermFactory.createApp(plus, x, TermFactory.createApp(plus, y, z));
    assertTrue(s.toString().equals("x + (y + z)"));
  }

  @Test
  public void testTimesLeftAssociativity() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    CalculationSymbol times = TheoryFactory.timesSymbol;
    Term s = TermFactory.createApp(times, TermFactory.createApp(times, x, y), z);
    assertTrue(s.toString().equals("x * y * z"));
  }

  @Test
  public void testTimesNotRightAssociative() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    CalculationSymbol times = TheoryFactory.timesSymbol;
    Term s = TermFactory.createApp(times, x, TermFactory.createApp(times, y, z));
    assertTrue(s.toString().equals("x * (y * z)"));
  }

  @Test
  public void testPlusInTimes() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    CalculationSymbol times = TheoryFactory.timesSymbol;
    Term s = TermFactory.createApp(times, TermFactory.createApp(plus, x, y), TermFactory.createApp(plus, y, x));
    assertTrue(s.toString().equals("(x + y) * (y + x)"));
  }

  @Test
  public void testTimesInPlus() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    CalculationSymbol times = TheoryFactory.timesSymbol;
    Term s = TermFactory.createApp(plus, TermFactory.createApp(times, x, y), TermFactory.createApp(times, y, x));
    assertTrue(s.toString().equals("x * y + y * x"));
  }

  @Test
  public void testComplexIntegerExpressionToString() {
    // (1 * (x + y)) * ( (x + -3) + ((y + x * 0) + z) )
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    CalculationSymbol times = TheoryFactory.timesSymbol;
    CalculationSymbol minus = TheoryFactory.minusSymbol;
    Term a = TermFactory.createApp(times, new IntegerValue(1), TermFactory.createApp(plus, x, y));
    Term b = TermFactory.createApp(plus, x, new IntegerValue(-3));
    Term c = TermFactory.createApp(minus, y, TermFactory.createApp(times, x, new IntegerValue(0)));
    Term d = TermFactory.createApp(plus, b, TermFactory.createApp(plus, c, z));
    Term s = TermFactory.createApp(times, a, d);
    assertTrue(s.toString().equals("1 * (x + y) * (x + -3 + (y - x * 0 + z))"));
  }

  @Test
  public void testDivModNoAssociativity() {
    // x / (y / z) and (x / y) / z
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    CalculationSymbol div = TheoryFactory.divSymbol;
    CalculationSymbol mod = TheoryFactory.modSymbol;
    Term a = TermFactory.createApp(div, x, TermFactory.createApp(div, y, z));
    Term b = TermFactory.createApp(div, TermFactory.createApp(div, x, y), z);
    Term c = TermFactory.createApp(mod, x, TermFactory.createApp(mod, y, z));
    Term d = TermFactory.createApp(mod, TermFactory.createApp(mod, x, y), z);
    assertTrue(a.toString().equals("x / (y / z)"));
    assertTrue(b.toString().equals("(x / y) / z"));
    assertTrue(c.toString().equals("x % (y % z)"));
    assertTrue(d.toString().equals("(x % y) % z"));
  }

  @Test
  public void testDivModTimesInteraction() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Variable z = TheoryFactory.createVar("z", TypeFactory.intSort);
    CalculationSymbol div = TheoryFactory.divSymbol;
    CalculationSymbol mod = TheoryFactory.modSymbol;
    CalculationSymbol times = TheoryFactory.timesSymbol;
    // x * y / z
    Term s = TermFactory.createApp(times, x, TermFactory.createApp(div, y, z));
    Term t = TermFactory.createApp(div, TermFactory.createApp(times, x, y), z);
    assertTrue(s.toString().equals("x * (y / z)"));
    assertTrue(t.toString().equals("(x * y) / z"));
    // x / y % z
    s = TermFactory.createApp(div, x, TermFactory.createApp(mod, y, z));
    t = TermFactory.createApp(mod, TermFactory.createApp(div, x, y), z);
    assertTrue(s.toString().equals("x / (y % z)"));
    assertTrue(t.toString().equals("(x / y) % z"));
    // x % y * z
    s = TermFactory.createApp(mod, x, TermFactory.createApp(times, y, z));
    t = TermFactory.createApp(times, TermFactory.createApp(mod, x, y), z);
    assertTrue(s.toString().equals("x % (y * z)"));
    assertTrue(t.toString().equals("(x % y) * z"));
    // x / y * z % u
    Variable u = TheoryFactory.createVar("u", TypeFactory.intSort);
    s = TermFactory.createApp(div, x, TermFactory.createApp(times, y, TermFactory.createApp(mod, z, u)));
    t = TermFactory.createApp(times, TermFactory.createApp(div, x, y), TermFactory.createApp(mod, z, u));
    assertTrue(s.toString().equals("x / (y * (z % u))"));
    assertTrue(t.toString().equals("(x / y) * (z % u)"));
    s = TermFactory.createApp(div, x, TermFactory.createApp(mod, TermFactory.createApp(times, y, z), u));
    assertTrue(s.toString().equals("x / ((y * z) % u)"));
    // x * y * z / u
    s = TermFactory.createApp(times, TermFactory.createApp(times, x, y), TermFactory.createApp(div, z, u));
    t = TermFactory.createApp(div, TermFactory.createApp(times, TermFactory.createApp(times, x, y), z), u);
    assertTrue(s.toString().equals("x * y * (z / u)"));
    assertTrue(t.toString().equals("(x * y * z) / u"));
  }

  @Test
  public void testPlusTimesMinusDivModEquality() {
    ArrayList<FunctionSymbol> theory = new ArrayList<FunctionSymbol>();
    theory.add(TheoryFactory.plusSymbol);
    theory.add(TheoryFactory.timesSymbol);
    theory.add(TheoryFactory.minusSymbol);
    theory.add(TheoryFactory.divSymbol);
    theory.add(TheoryFactory.modSymbol);
    ArrayList<FunctionSymbol> fake = new ArrayList<FunctionSymbol>();
    Type in = TypeFactory.intSort;
    fake.add(TermFactory.createConstant("+", TypeFactory.createArrow(in, TypeFactory.createArrow(in, in))));
    fake.add(TermFactory.createConstant("*", TypeFactory.createArrow(in, TypeFactory.createArrow(in, in))));
    fake.add(TermFactory.createConstant("-", TypeFactory.createArrow(in, in)));
    fake.add(TermFactory.createConstant("/", TypeFactory.createArrow(in, TypeFactory.createArrow(in, in))));
    fake.add(TermFactory.createConstant("%", TypeFactory.createArrow(in, TypeFactory.createArrow(in, in))));

    assertTrue(theory.get(0).equals(TheoryFactory.plusSymbol));
    assertTrue(theory.get(1).equals(TheoryFactory.timesSymbol));
    assertTrue(theory.get(2).equals(TheoryFactory.minusSymbol));
    assertTrue(theory.get(3).equals(TheoryFactory.divSymbol));
    assertTrue(theory.get(4).equals(TheoryFactory.modSymbol));

    for (int i = 0; i < theory.size(); i++) {
      assertTrue(theory.get(i).equals(theory.get(i)), "theory " + i + " is not equal to itself");
      assertFalse(fake.get(i).equals(theory.get(i)), "theory " + i + " equals its fake part");
      assertFalse(theory.get(i).equals(fake.get(i)), "fake " + i + " equals theory " + i);
      for (int j = i+1; j < theory.size(); j++) {
        assertFalse(theory.get(i).equals(theory.get(j)), "theory " + j + " = theory " + i);
        assertFalse(theory.get(j).equals(theory.get(i)), "theory " + i + " = theory " + j);
      }
    }
  }
}
