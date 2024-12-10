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

package cora.rwinduction.parser;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.util.FixedList;
import charlie.terms.Term;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.Equation;

class ExtendedTermParserTest {
  TRS trs = CoraInputReader.readTrsFromString (
    "sum :: Int -> Int\n" +
    "sum(x) -> 0         | x ≤ 0\n" +
    "sum(x) -> x + sum(x - 1) | x > 0"
  );

  @Test
  public void testEquationWithConstraint() {
    Equation equation = ExtendedTermParser.parseEquation("sum(x) ≈ sum(y) | x = y", trs);
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(x)"));
    assertTrue(r.toString().equals("sum(y)"));
    assertTrue(c.toString().equals("x = y"));
    assertTrue(equation.getRenaming().domain().size() == 2);
    assertTrue(l.queryArgument(1) == equation.getRenaming().getVariable("x"));
    assertTrue(r.queryArgument(1) == equation.getRenaming().getVariable("y"));
    assertTrue(c.queryArgument(1) == equation.getRenaming().getVariable("x"));
    assertTrue(c.queryArgument(2) == equation.getRenaming().getVariable("y"));
  }

  @Test
  public void testEquationWithoutConstraint() {
    Equation equation = ExtendedTermParser.parseEquation("sum(y) -><- sum(x+y)", trs);
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(y)"));
    assertTrue(r.toString().equals("sum(x + y)"));
    assertTrue(c.toString().equals("true"));
    assertTrue(l.queryArgument(1) == equation.getRenaming().getVariable("y"));
    assertTrue(r.queryArgument(1).queryArgument(1) == equation.getRenaming().getVariable("x"));
    assertTrue(r.queryArgument(1).queryArgument(2) == equation.getRenaming().getVariable("y"));
  }

  @Test
  public void testEquationWithEqualsSymbol() {
    Equation equation = ExtendedTermParser.parseEquation("sum(x) = sum(y) | x = y", trs);
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(x)"));
    assertTrue(r.toString().equals("sum(y)"));
    assertTrue(c.toString().equals("x = y"));
    assertTrue(equation.getRenaming().domain().size() == 2);

    equation = ExtendedTermParser.parseEquation("sum(y) = sum(y+y)", trs);
    assertTrue(equation.getLhs().toString().equals("sum(y)"));
    assertTrue(equation.getRhs().toString().equals("sum(y + y)"));
    assertTrue(equation.getRenaming().domain().size() == 1);
  }

  @Test
  public void testEquationDoesNotEndThere() {
    assertThrows(charlie.exceptions.ParseException.class, () ->
      ExtendedTermParser.parseEquation("sum(x) = sum(y) | x = y sum(x)", trs));
    assertThrows(charlie.exceptions.ParseException.class, () ->
      ExtendedTermParser.parseEquation("sum(1) = sum(2) x = y", trs));
  }

  @Test
  public void testReadMultipleEquations() {
    FixedList<Equation> lst = ExtendedTermParser.parseEquationList(
      "sum(x) ≈ sum(y) | x = y ; sum(y) -><- sum(x+y) ; sum(1) = sum(2)", trs);
    assertTrue(lst.size() == 3);
    assertTrue(lst.get(0).toString().equals("sum(x) ≈ sum(y) | x = y"));
    assertTrue(lst.get(1).toString().equals("sum(y) ≈ sum(x + y) | true"));
    assertTrue(lst.get(2).toString().equals("sum(1) ≈ sum(2) | true"));
    lst = ExtendedTermParser.parseEquationList("sum(x) ≈ sum(y) | x = y ;", trs);
    assertTrue(lst.size() == 1);
    assertTrue(lst.get(0).toString().equals("sum(x) ≈ sum(y) | x = y"));
  }
}
