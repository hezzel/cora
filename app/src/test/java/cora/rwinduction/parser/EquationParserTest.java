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

import java.util.Set;

import charlie.exceptions.ParseException;
import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.EquationContext;

class EquationParserTest {
  TRS trs = CoraInputReader.readTrsFromString (
    "sum :: Int -> Int\n" +
    "sum(x) -> 0         | x ≤ 0\n" +
    "sum(x) -> x + sum(x - 1) | x > 0"
  );

  @Test
  public void testEquationWithConstraint() {
    Pair<Equation,Renaming> p = EquationParser.parseEquation("sum(x) ≈ sum(y) | x = y", trs);
    Equation equation = p.fst();
    Renaming renaming = p.snd();
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(x)"));
    assertTrue(r.toString().equals("sum(y)"));
    assertTrue(c.toString().equals("x = y"));
    assertTrue(renaming.domain().size() == 2);
    assertTrue(l.queryArgument(1) == renaming.getVariable("x"));
    assertTrue(r.queryArgument(1) == renaming.getVariable("y"));
    assertTrue(c.queryArgument(1) == renaming.getVariable("x"));
    assertTrue(c.queryArgument(2) == renaming.getVariable("y"));
  }

  @Test
  public void testEquationContextWithoutConstraint() {
    EquationContext context = EquationParser.parseEquationData("sum(y) -><- sum(x+y)", trs, 15);
    Term l = context.getEquation().getLhs();
    Term r = context.getEquation().getRhs();
    Term c = context.getEquation().getConstraint();
    assertTrue(l.toString().equals("sum(y)"));
    assertTrue(r.toString().equals("sum(x + y)"));
    assertTrue(c.toString().equals("true"));
    assertTrue(context.getIndex() == 15);
    assertFalse(context.hasExtraTerms());
    assertTrue(l.queryArgument(1) == context.getRenamingCopy().getVariable("y"));
    assertTrue(r.queryArgument(1).queryArgument(1) == context.getRenamingCopy().getVariable("x"));
    assertTrue(r.queryArgument(1).queryArgument(2) == context.getRenamingCopy().getVariable("y"));
  }

  @Test
  public void testEquationWithEqualsSymbol() {
    EquationContext context = EquationParser.parseEquationData("sum(x) = sum(y) | x = y", trs, 1);
    Term l = context.getEquation().getLhs();
    Term r = context.getEquation().getRhs();
    Term c = context.getEquation().getConstraint();
    assertTrue(l.toString().equals("sum(x)"));
    assertTrue(r.toString().equals("sum(y)"));
    assertTrue(c.toString().equals("x = y"));
    assertTrue(context.getRenamingCopy().domain().size() == 2);

    Pair<Equation,Renaming> p = EquationParser.parseEquation("sum(y) = sum(y+y)", trs);
    assertTrue(p.fst().getLhs().toString().equals("sum(y)"));
    assertTrue(p.fst().getRhs().toString().equals("sum(y + y)"));
    assertTrue(p.snd().domain().size() == 1);
  }

  @Test
  public void testEquationDoesNotEndThere() {
    assertThrows(charlie.exceptions.ParseException.class, () ->
      EquationParser.parseEquation("sum(x) = sum(y) | x = y sum(x)", trs));
    assertThrows(charlie.exceptions.ParseException.class, () ->
      EquationParser.parseEquationData("sum(1) = sum(2) x = y", trs, 2));
  }

  @Test
  public void testReadMultipleEquations() {
    FixedList<EquationContext> lst = EquationParser.parseEquationList(
      "sum(x) ≈ sum(y) | x = y ; sum(y) -><- sum(x+y) ; sum(1) = sum(2)", trs);
    assertTrue(lst.size() == 3);
    assertTrue(lst.get(0).toString().equals("E1: (• , sum(x) ≈ sum(y) | x = y , •)"));
    assertTrue(lst.get(1).toString().equals("E2: (• , sum(y) ≈ sum(x + y) , •)"));
    assertTrue(lst.get(2).toString().equals("E3: (• , sum(1) ≈ sum(2) , •)"));
    assertTrue(lst.get(0).getIndex() == 1);
    assertTrue(lst.get(1).getIndex() == 2);
    assertTrue(lst.get(2).getIndex() == 3);
    lst = EquationParser.parseEquationList("sum(x) ≈ sum(y) | x = y ;", trs);
    assertTrue(lst.size() == 1);
    assertTrue(lst.get(0).toString().equals("E1: (• , sum(x) ≈ sum(y) | x = y , •)"));
  }
}
