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
import charlie.util.FixedList;
import charlie.terms.*;
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
    Equation equation = ExtendedTermParser.parseEquation("sum(x) ≈ sum(y) | x = y", trs, 3);
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(x)"));
    assertTrue(r.toString().equals("sum(y)"));
    assertTrue(c.toString().equals("x = y"));
    assertTrue(equation.getIndex() == 3);
    assertTrue(equation.getRenaming().domain().size() == 2);
    assertTrue(l.queryArgument(1) == equation.getRenaming().getVariable("x"));
    assertTrue(r.queryArgument(1) == equation.getRenaming().getVariable("y"));
    assertTrue(c.queryArgument(1) == equation.getRenaming().getVariable("x"));
    assertTrue(c.queryArgument(2) == equation.getRenaming().getVariable("y"));
  }

  @Test
  public void testEquationWithoutConstraint() {
    Equation equation = ExtendedTermParser.parseEquation("sum(y) -><- sum(x+y)", trs, 15);
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(y)"));
    assertTrue(r.toString().equals("sum(x + y)"));
    assertTrue(c.toString().equals("true"));
    assertTrue(equation.getIndex() == 15);
    assertTrue(l.queryArgument(1) == equation.getRenaming().getVariable("y"));
    assertTrue(r.queryArgument(1).queryArgument(1) == equation.getRenaming().getVariable("x"));
    assertTrue(r.queryArgument(1).queryArgument(2) == equation.getRenaming().getVariable("y"));
  }

  @Test
  public void testEquationWithEqualsSymbol() {
    Equation equation = ExtendedTermParser.parseEquation("sum(x) = sum(y) | x = y", trs, 1);
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(x)"));
    assertTrue(r.toString().equals("sum(y)"));
    assertTrue(c.toString().equals("x = y"));
    assertTrue(equation.getRenaming().domain().size() == 2);

    equation = ExtendedTermParser.parseEquation("sum(y) = sum(y+y)", trs, 1);
    assertTrue(equation.getLhs().toString().equals("sum(y)"));
    assertTrue(equation.getRhs().toString().equals("sum(y + y)"));
    assertTrue(equation.getRenaming().domain().size() == 1);
  }

  @Test
  public void testEquationDoesNotEndThere() {
    assertThrows(charlie.exceptions.ParseException.class, () ->
      ExtendedTermParser.parseEquation("sum(x) = sum(y) | x = y sum(x)", trs, 1));
    assertThrows(charlie.exceptions.ParseException.class, () ->
      ExtendedTermParser.parseEquation("sum(1) = sum(2) x = y", trs, 2));
  }

  @Test
  public void testReadMultipleEquations() {
    FixedList<Equation> lst = ExtendedTermParser.parseEquationList(
      "sum(x) ≈ sum(y) | x = y ; sum(y) -><- sum(x+y) ; sum(1) = sum(2)", trs);
    assertTrue(lst.size() == 3);
    assertTrue(lst.get(0).toString().equals("1: sum(x) ≈ sum(y) | x = y"));
    assertTrue(lst.get(1).toString().equals("2: sum(y) ≈ sum(x + y) | true"));
    assertTrue(lst.get(2).toString().equals("3: sum(1) ≈ sum(2) | true"));
    assertTrue(lst.get(0).getIndex() == 1);
    assertTrue(lst.get(1).getIndex() == 2);
    assertTrue(lst.get(2).getIndex() == 3);
    lst = ExtendedTermParser.parseEquationList("sum(x) ≈ sum(y) | x = y ;", trs);
    assertTrue(lst.size() == 1);
    assertTrue(lst.get(0).toString().equals("1: sum(x) ≈ sum(y) | x = y"));
  }

  @Test
  public void testParseSubstitution() {
    Variable x = TermFactory.createVar(CoraInputReader.readType("Int"));
    Variable z = TermFactory.createVar(CoraInputReader.readType("Int"));
    Renaming keys = new Renaming(Set.of());
    keys.setName(x, "x");
    keys.setName(z, "z");
    Renaming values = new Renaming(Set.of());
    Term t1 = CoraInputReader.readTermAndUpdateNaming("x + sum(y)", values, trs);
    Term t2 = CoraInputReader.readTermAndUpdateNaming("sum(3)", values, trs);
    Substitution subst =
      ExtendedTermParser.parseSubstitution("[x := x + sum(y), z := sum(3)]", trs, keys, values);
    assertTrue(subst.get(x).equals(t1));
    assertTrue(subst.get(z).equals(t2));
  }

  @Test
  public void testMissingKey() {
    Renaming keys = new Renaming(Set.of());
    keys.setName(TermFactory.createVar("z", CoraInputReader.readType("Int")), "z");
    Renaming values = new Renaming(Set.of());
    Term t1 = CoraInputReader.readTermAndUpdateNaming("x + sum(y)", values, trs);
    assertThrows(ParseException.class, () ->
      ExtendedTermParser.parseSubstitution("[x := x + sum(y), z := sum(3)]", trs, keys, values));
  }

  @Test
  public void testMissingVariableInValue() {
    Variable x = TermFactory.createVar(CoraInputReader.readType("Int"));
    Variable z = TermFactory.createVar(CoraInputReader.readType("Int"));
    Renaming keys = new Renaming(Set.of());
    keys.setName(x, "x");
    keys.setName(z, "z");
    Renaming values = new Renaming(Set.of());
    Substitution subst =
      ExtendedTermParser.parseSubstitution("[x := x + sum(y), z := sum(3)]", trs, keys, values);
    assertTrue(subst.get(x).toString().equals("x + sum(y)"));
    assertTrue(subst.get(z).toString().equals("sum(3)"));
    assertTrue(values.getReplaceable("x") != null);
    assertTrue(values.getReplaceable("y") != null);
    assertTrue(values.getReplaceable("z") == null);
  }

  @Test
  public void testIllTypedSubstitution() {
    Variable z = TermFactory.createVar(CoraInputReader.readType("Bool"));
    Renaming keys = new Renaming(Set.of());
    keys.setName(z, "z");
    Renaming values = new Renaming(Set.of());
    assertThrows(ParseException.class, () ->
      ExtendedTermParser.parseSubstitution("[z := sum(3)]", trs, keys, values));
  }
}
