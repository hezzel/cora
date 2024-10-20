package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.terms.Term;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.data.Equation;

class CommandParserTest {

  TRS trs = CoraInputReader.readTrsFromString (
    "sum :: Int -> Int\n" +
    "sum(x) -> 0         | x ≤ 0\n" +
    "sum(x) -> x + sum(x - 1) | x > 0"
  );

  @Test
  public void testEquationWithConstraint() {
    Equation equation = CommandParser.parseEquation("sum(x) = sum(y) | x = y", trs);
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(x)"));
    assertTrue(r.toString().equals("sum(y)"));
    assertTrue(c.toString().equals("x = y"));
    assertTrue(equation.getVarNaming().domain().size() == 2);
    assertTrue(l.queryArgument(1) == equation.getVarNaming().getVariable("x"));
    assertTrue(r.queryArgument(1) == equation.getVarNaming().getVariable("y"));
    assertTrue(c.queryArgument(1) == equation.getVarNaming().getVariable("x"));
    assertTrue(c.queryArgument(2) == equation.getVarNaming().getVariable("y"));
  }

  @Test
  public void testEquationWithoutConstraint() {
    Equation equation = CommandParser.parseEquation("sum(y) = sum(x+y)", trs);
    Term l = equation.getLhs();
    Term r = equation.getRhs();
    Term c = equation.getConstraint();
    assertTrue(l.toString().equals("sum(y)"));
    assertTrue(r.toString().equals("sum(x + y)"));
    assertTrue(c.toString().equals("true"));
    assertTrue(l.queryArgument(1) == equation.getVarNaming().getVariable("y"));
    assertTrue(r.queryArgument(1).queryArgument(1) == equation.getVarNaming().getVariable("x"));
    assertTrue(r.queryArgument(1).queryArgument(2) == equation.getVarNaming().getVariable("y"));
  }
}
