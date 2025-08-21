/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.parser.lib.ParsingException;
import charlie.terms.replaceable.MutableRenaming;
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
    Pair<Equation,MutableRenaming> p = EquationParser.parseEquation("sum(x) ≈ sum(y) | x = y", trs);
    Equation equation = p.fst();
    MutableRenaming renaming = p.snd();
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(x)"));
    assertTrue(r.toString().equals("sum(y)"));
    assertTrue(c.toString().equals("x = y"));
    assertTrue(renaming.domain().size() == 2);
    assertTrue(l.queryArgument(1) == renaming.getReplaceable("x"));
    assertTrue(r.queryArgument(1) == renaming.getReplaceable("y"));
    assertTrue(c.queryArgument(1) == renaming.getReplaceable("x"));
    assertTrue(c.queryArgument(2) == renaming.getReplaceable("y"));
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
    assertTrue(l.queryArgument(1) == context.getRenaming().getReplaceable("y"));
    assertTrue(r.queryArgument(1).queryArgument(1) == context.getRenaming().getReplaceable("x"));
    assertTrue(r.queryArgument(1).queryArgument(2) == context.getRenaming().getReplaceable("y"));
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
    assertTrue(context.getRenaming().domain().size() == 2);

    Pair<Equation,MutableRenaming> p = EquationParser.parseEquation("sum(y) = sum(y+y)", trs);
    assertTrue(p.fst().getLhs().toString().equals("sum(y)"));
    assertTrue(p.fst().getRhs().toString().equals("sum(y + y)"));
    assertTrue(p.snd().domain().size() == 1);
  }

  @Test
  public void testEquationDoesNotEndThere() {
    assertThrows(charlie.parser.lib.ParsingException.class, () ->
      EquationParser.parseEquation("sum(x) = sum(y) | x = y sum(x)", trs));
    assertThrows(charlie.parser.lib.ParsingException.class, () ->
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

  @Test
  public void testReadEquationContext() {
    EquationContext ec =
      EquationParser.parseEquationContext("(*, sum(x) [=] sum(y),sum(y) )", 3, trs);
    assertTrue(ec.toString().equals("E3: (• , sum(x) ≈ sum(y) , sum(y))"));
    ec = EquationParser.parseEquationContext("(sum(x+y) , sum(x) = sum(y) | x >= y,•)", 7, trs);
    assertTrue(ec.toString().equals("E7: (sum(x + y) , sum(x) ≈ sum(y) | x ≥ y , •)"));
  }
}
