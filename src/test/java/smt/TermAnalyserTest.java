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

package cora.smt;

import org.junit.Test;
import static org.junit.Assert.*;

import cora.exceptions.UnsupportedTheoryError;
import cora.types.TypeFactory;
import cora.terms.*;

public class TermAnalyserTest {
  @Test(expected = UnsupportedTheoryError.class)
  public void testIncompleteCalculate() {
    TermAnalyser.calculate(TheoryFactory.andSymbol.apply(TheoryFactory.createValue(false)));
  }

  @Test
  public void testAndOrCalculate() {
    CalculationSymbol a = TheoryFactory.andSymbol;
    CalculationSymbol o = TheoryFactory.orSymbol;

    Term tr = TheoryFactory.createValue(true);
    Term fa = TheoryFactory.createValue(false);
    Term x = TheoryFactory.createVar("x", TypeFactory.boolSort);
    
    // false ∧ x -- we do NOT reduce this to false
    Term t = TermFactory.createApp(a, fa, x);
    assertTrue(TermAnalyser.calculate(t) == null);

    // false ∧ (true ∧ false) -- we do NOT reduce this, because it is not a single step
    t = TermFactory.createApp(a, fa, TermFactory.createApp(a, tr, fa));
    assertTrue(TermAnalyser.calculate(t) == null);

    // false ∧ true
    t = TermFactory.createApp(a, fa, tr);
    assertTrue(TermAnalyser.calculate(t).equals(fa));

    // false ∨ true
    t = TermFactory.createApp(o, fa, tr);
    assertTrue(TermAnalyser.calculate(t).equals(tr));
  }

  @Test
  public void testPlusCalculate() {
    CalculationSymbol p = TheoryFactory.plusSymbol;
    Term x = TheoryFactory.createVar("x", TypeFactory.intSort);

    // +(x, 1)
    Term t = TermFactory.createApp(p, x, TheoryFactory.createValue(1));
    assertTrue(TermAnalyser.calculate(t) == null);

    // +(-7, 3)
    t = TermFactory.createApp(p, TheoryFactory.createValue(-7), TheoryFactory.createValue(3));
    assertTrue(TermAnalyser.calculate(t).equals(TheoryFactory.createValue(-4)));
  }
}

