/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import cora.exceptions.*;
import cora.types.TypeFactory;
import cora.types.Type;

public class IntegerCalculationSymbolTest extends TermTestFoundation {
  @Test
  public void testPlusBasics() {
    CalculationSymbol p = TheoryFactory.plusSymbol;
    assertTrue(p.queryType().toString().equals("Int → Int → Int"));
    assertTrue(p.queryInfixPriority() == CalculationSymbol.INFIX_PLUS);
    assertTrue(p.queryName().equals("+"));
    assertTrue(p.toString().equals("[+]"));
    assertTrue(p.toUniqueString().equals("+{Int → Int → Int}#calc"));
    assertTrue(p.queryArity() == 2);
  }

  @Test
  public void testTimesBasics() {
    CalculationSymbol t = TheoryFactory.timesSymbol;
    assertTrue(t.queryType().toString().equals("Int → Int → Int"));
    assertTrue(t.queryInfixPriority() == CalculationSymbol.INFIX_TIMES);
    assertTrue(t.queryName().equals("*"));
    assertTrue(t.toString().equals("[*]"));
    assertTrue(t.toUniqueString().equals("*{Int → Int → Int}#calc"));
    assertTrue(t.queryArity() == 2);
  }

  @Test
  public void testMinusBasics() {
    CalculationSymbol m = TheoryFactory.minusSymbol;
    assertTrue(m.queryType().toString().equals("Int → Int"));
    assertTrue(m.queryInfixPriority() == CalculationSymbol.INFIX_NONE);
    assertTrue(m.queryName().equals("-"));
    assertTrue(m.toString().equals("[-]"));
    assertTrue(m.toUniqueString().equals("-{Int → Int}#calc"));
    assertTrue(m.queryArity() == 1);
  }

  @Test
  public void testDivBasics() {
    CalculationSymbol p = TheoryFactory.divSymbol;
    assertTrue(p.queryType().toString().equals("Int → Int → Int"));
    assertTrue(p.queryInfixPriority() == CalculationSymbol.INFIX_DIVMOD);
    assertTrue(p.queryName().equals("/"));
    assertTrue(p.toString().equals("[/]"));
    assertTrue(p.toUniqueString().equals("/{Int → Int → Int}#calc"));
    assertTrue(p.queryArity() == 2);
  }

  @Test
  public void testModBasics() {
    CalculationSymbol p = TheoryFactory.modSymbol;
    assertTrue(p.queryType().toString().equals("Int → Int → Int"));
    assertTrue(p.queryInfixPriority() == CalculationSymbol.INFIX_DIVMOD);
    assertTrue(p.queryName().equals("%"));
    assertTrue(p.toString().equals("[%]"));
    assertTrue(p.toUniqueString().equals("%{Int → Int → Int}#calc"));
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
  public void testSimpleMinusToString() {
    CalculationSymbol f = TheoryFactory.minusSymbol;
    assertTrue(f.toString().equals("[-]"));
    Value v = new IntegerValue(3);
    assertTrue(f.apply(v).toString().equals("-3"));
    Var x = new Var("x", TypeFactory.intSort);
    assertTrue(f.apply(x).toString().equals("-x"));
  }

  @Test
  public void testMinusWithNegativeValue() {
    CalculationSymbol f = TheoryFactory.minusSymbol;
    assertTrue(f.toString().equals("[-]"));
    Value v = new IntegerValue(-3);
    assertTrue(f.apply(v).toString().equals("-(-3)"));
  }

  @Test
  public void testMinusWithComplexArgument() {
    CalculationSymbol m = TheoryFactory.minusSymbol;
    CalculationSymbol p = TheoryFactory.plusSymbol;
    CalculationSymbol t = TheoryFactory.timesSymbol;
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Term s = m.apply(p.apply(x).apply(y));
    assertTrue(s.toString().equals("-(x + y)"));
    s = m.apply(t.apply(x).apply(y));
    assertTrue(s.toString().equals("-(x * y)"));
  }

  @Test
  public void testPrintPlusNegativeValue() {
    Var x = new Var("x", TypeFactory.intSort);
    Term s = new Application(TheoryFactory.plusSymbol, x, new IntegerValue(-3));
    assertTrue(s.toString().equals("x - 3"));
  }

  @Test
  public void testPrintPlusNegativeAddition() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol p = TheoryFactory.plusSymbol;
    Term s = new Application(p, x, new Application(TheoryFactory.minusSymbol,
      new Application(p, y, z)));
    assertTrue(s.toString().equals("x - (y + z)"));
  }

  @Test
  public void testPrintPlusNegativeMultiplication() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    Term s = new Application(TheoryFactory.plusSymbol, x, new Application(TheoryFactory.minusSymbol,
      new Application(TheoryFactory.timesSymbol, y, z)));
    assertTrue(s.toString().equals("x - y * z"));
  }

  @Test
  public void testPlusLeftAssociativity() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    Term s = new Application(plus, new Application(plus, x, y), z);
    assertTrue(s.toString().equals("x + y + z"));
  }

  @Test
  public void testPlusNotRightAssociative() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    Term s = new Application(plus, x, new Application(plus, y, z));
    assertTrue(s.toString().equals("x + (y + z)"));
  }

  @Test
  public void testTimesLeftAssociativity() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol times = TheoryFactory.timesSymbol;
    Term s = new Application(times, new Application(times, x, y), z);
    assertTrue(s.toString().equals("x * y * z"));
  }

  @Test
  public void testTimesNotRightAssociative() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol times = TheoryFactory.timesSymbol;
    Term s = new Application(times, x, new Application(times, y, z));
    assertTrue(s.toString().equals("x * (y * z)"));
  }

  @Test
  public void testPlusInTimes() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    CalculationSymbol times = TheoryFactory.timesSymbol;
    Term s = new Application(times, new Application(plus, x, y), new Application(plus, y, x));
    assertTrue(s.toString().equals("(x + y) * (y + x)"));
  }

  @Test
  public void testTimesInPlus() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    CalculationSymbol times = TheoryFactory.timesSymbol;
    Term s = new Application(plus, new Application(times, x, y), new Application(times, y, x));
    assertTrue(s.toString().equals("x * y + y * x"));
  }

  @Test
  public void testComplexIntegerExpressionToString() {
    // (1 * (x + y)) * ( (x + -3) + ((y + x * 0) + z) )
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol plus = TheoryFactory.plusSymbol;
    CalculationSymbol times = TheoryFactory.timesSymbol;
    CalculationSymbol minus = TheoryFactory.minusSymbol;
    Term a = new Application(times, new IntegerValue(1), new Application(plus, x, y));
    Term b = new Application(plus, x, new IntegerValue(-3));
    Term c = new Application(plus, y, minus.apply(new Application(times, x, new IntegerValue(0))));
    Term d = new Application(plus, b, new Application(plus, c, z));
    Term s = new Application(times, a, d);
    assertTrue(s.toString().equals("1 * (x + y) * (x - 3 + (y - x * 0 + z))"));
  }

  @Test
  public void testDivModNoAssociativity() {
    // x / (y / z) and (x / y) / z
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol div = TheoryFactory.divSymbol;
    CalculationSymbol mod = TheoryFactory.modSymbol;
    Term a = new Application(div, x, new Application(div, y, z));
    Term b = new Application(div, new Application(div, x, y), z);
    Term c = new Application(mod, x, new Application(mod, y, z));
    Term d = new Application(mod, new Application(mod, x, y), z);
    assertTrue(a.toString().equals("x / (y / z)"));
    assertTrue(b.toString().equals("(x / y) / z"));
    assertTrue(c.toString().equals("x % (y % z)"));
    assertTrue(d.toString().equals("(x % y) % z"));
  }

  @Test
  public void testDivModTimesInteraction() {
    Var x = new Var("x", TypeFactory.intSort);
    Var y = new Var("y", TypeFactory.intSort);
    Var z = new Var("z", TypeFactory.intSort);
    CalculationSymbol div = TheoryFactory.divSymbol;
    CalculationSymbol mod = TheoryFactory.modSymbol;
    CalculationSymbol times = TheoryFactory.timesSymbol;
    // x * y / z
    Term s = new Application(times, x, new Application(div, y, z));
    Term t = new Application(div, new Application(times, x, y), z);
    assertTrue(s.toString().equals("x * (y / z)"));
    assertTrue(t.toString().equals("(x * y) / z"));
    // x / y % z
    s = new Application(div, x, new Application(mod, y, z));
    t = new Application(mod, new Application(div, x, y), z);
    assertTrue(s.toString().equals("x / (y % z)"));
    assertTrue(t.toString().equals("(x / y) % z"));
    // x % y * z
    s = new Application(mod, x, new Application(times, y, z));
    t = new Application(times, new Application(mod, x, y), z);
    assertTrue(s.toString().equals("x % (y * z)"));
    assertTrue(t.toString().equals("(x % y) * z"));
    // x / y * z % u
    Var u = new Var("u", TypeFactory.intSort);
    s = new Application(div, x, new Application(times, y, new Application(mod, z, u)));
    t = new Application(times, new Application(div, x, y), new Application(mod, z, u));
    assertTrue(s.toString().equals("x / (y * (z % u))"));
    assertTrue(t.toString().equals("(x / y) * (z % u)"));
    s = new Application(div, x, new Application(mod, new Application(times, y, z), u));
    assertTrue(s.toString().equals("x / ((y * z) % u)"));
    // x * y * z / u
    s = new Application(times, new Application(times, x, y), new Application(div, z, u));
    t = new Application(div, new Application(times, new Application(times, x, y), z), u);
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
    fake.add(new Constant("+", arrowType(in, arrowType(in, in))));
    fake.add(new Constant("*", arrowType(in, arrowType(in, in))));
    fake.add(new Constant("-", arrowType(in, in)));
    fake.add(new Constant("/", arrowType(in, arrowType(in, in))));
    fake.add(new Constant("%", arrowType(in, arrowType(in, in))));

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
