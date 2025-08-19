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

package cora.termination.dependency_pairs;

import charlie.types.TypeFactory;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.reader.CoraInputReader;

import java.util.Set;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class DPTest {
  private TRS trs = CoraInputReader.readTrsFromString(
    "eval :: Int -> Int -> Int\n" +
    "eval(x, y) -> eval(x - 1, y) | x>y");

  @Test
  void testCreateFullDP() {
    MutableRenaming renaming = new MutableRenaming(Set.of());
    Term lhs = CoraInputReader.readTermAndUpdateNaming("eval(x, y)", renaming, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, trs);
    Term constraint = CoraInputReader.readTerm("x > y", renaming, trs);
    Set<Variable> vars = Set.of((Variable)renaming.getReplaceable("x"),
                                (Variable)renaming.getReplaceable("y"));
    DP dp = new DP(lhs, rhs, constraint, vars);
    assertTrue(dp.ustr().equals("eval(x, y) ➡ eval(x - 1, y) | x > y"));
  }

  @Test
  void testCreateFullDPWithExtraVariable() {
    MutableRenaming renaming = new MutableRenaming(Set.of());
    Term lhs = CoraInputReader.readTermAndUpdateNaming("eval(x, y)", renaming, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, trs);
    Term constraint = CoraInputReader.readTerm("x > y", renaming, trs);
    Set<Variable> vars = Set.of((Variable)renaming.getReplaceable("x"),
                                (Variable)renaming.getReplaceable("y"),
                                TheoryFactory.createVar("z", TypeFactory.boolSort));
    DP dp = new DP(lhs, rhs, constraint, vars);
    assertTrue(dp.ustr().equals("eval(x, y) ➡ eval(x - 1, y) | x > y"));
  }

  @Test
  void testDeduceVariables() {
    MutableRenaming renaming = new MutableRenaming(Set.of());
    Term lhs = CoraInputReader.readTermAndUpdateNaming("eval(x, y)", renaming, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, trs);
    Term constraint = CoraInputReader.readTerm("x > y", renaming, trs);
    DP dp = new DP(lhs, rhs, constraint);
    assertTrue(dp.ustr().equals("eval(x, y) ➡ eval(x - 1, y) | x > y"));
  }

  @Test
  void testDeduceConstraint() {
    MutableRenaming renaming = new MutableRenaming(Set.of());
    Term lhs = CoraInputReader.readTermAndUpdateNaming("eval(x, x)", renaming, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, trs);
    DP dp = new DP(lhs, rhs);
    assertTrue(dp.ustr().equals("eval(x, x) ➡ eval(x - 1, y) | true"));
  }

  @Test
  public void testAllVariables() {
    MutableRenaming renaming = new MutableRenaming(Set.of());
    Term lhs = CoraInputReader.readTermAndUpdateNaming("eval(x, y)", renaming, trs);
    Term rhs = CoraInputReader.readTerm("eval(x-1, y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > y ∧ z =_Int z", renaming, trs);
    Set<Variable> vars = Set.of((Variable)renaming.getReplaceable("x"),
                                (Variable)renaming.getReplaceable("y"),
                                (Variable)renaming.getReplaceable("z"),
                                TheoryFactory.createVar("a", TypeFactory.boolSort));
    DP dp = new DP(lhs, rhs, constraint, vars);
    Set<Variable> allvars = dp.getAllVariables();
    assertTrue(allvars.size() == 3);
    assertTrue(allvars.contains((Variable)renaming.getReplaceable("x")));
    assertTrue(allvars.contains((Variable)renaming.getReplaceable("y")));
    assertTrue(allvars.contains((Variable)renaming.getReplaceable("z")));
    assertFalse(allvars.contains((Variable)renaming.getReplaceable("a")));
  }

  @Test
  public void testRenaming() {
    MutableRenaming renaming = new MutableRenaming(Set.of());
    Term lhs = CoraInputReader.readTermAndUpdateNaming("eval(x, y)", renaming, trs);
    Term rhs = CoraInputReader.readTermAndUpdateNaming("eval(x-1, y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > y ∧ z =_Int z", renaming, trs);
    Set<Variable> vars = new TreeSet<Variable>();
    vars.add((Variable)renaming.getReplaceable("x"));
    vars.add((Variable)renaming.getReplaceable("y"));
    vars.add((Variable)renaming.getReplaceable("z"));
    vars.add(TheoryFactory.createVar("a", TypeFactory.boolSort));
    DP dp = new DP(lhs, rhs, constraint, vars);
    DP dp2 = dp.getRenamed();
    assertTrue(dp2.lvars().size() == 3);
    assertFalse(dp.toString().equals(dp2.toString()));
    TermPrinter printer = new TermPrinter(Set.of());
    renaming = printer.generateUniqueNaming(dp.lhs(), dp.rhs(), dp.constraint(),
      dp2.lhs(), dp2.rhs(), dp2.constraint());
    Printer pr = PrinterFactory.createUnicodePrinter(trs);
    pr.add(dp.makePrintableWith(renaming), "\n", dp2.makePrintableWith(renaming));
    assertTrue(pr.toString().equals(
      "eval(x__1, y__1) ➡ eval(x__1 - 1, y__1) | x__1 > y__1 ∧ z__1 = z__1\n" +
      "eval(x__2, y__2) ➡ eval(x__2 - 1, y__2) | x__2 > y__2 ∧ z__2 = z__2"));
  }

  @Test
  public void testPrint() {
    MutableRenaming renaming1 = new MutableRenaming(Set.of());
    Term lhs = CoraInputReader.readTermAndUpdateNaming("eval(x, y)", renaming1, trs);
    MutableRenaming renaming = new MutableRenaming(Set.of());
    Term rhs = CoraInputReader.readTermAndUpdateNaming("eval(x-1, y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > z", renaming, trs);
    Set<Variable> vars = new TreeSet<Variable>();
    vars.add((Variable)renaming.getReplaceable("x"));
    vars.add((Variable)renaming.getReplaceable("y"));
    vars.add((Variable)renaming.getReplaceable("z"));
    vars.add(TheoryFactory.createVar("a", TypeFactory.boolSort));
    DP dp = new DP(lhs, rhs, constraint, vars);
    Printer printer = PrinterFactory.createPlainPrinter(trs);
    dp.print(printer);
    assertTrue(printer.toString().equals(
      "eval(x__1, y__1) => eval(x__2 - 1, y__2) | x__2 > z { y__2 }"));
    printer = PrinterFactory.createUnicodePrinter(trs);
    renaming.setName(renaming1.getReplaceable("x"), "a");
    renaming.setName(renaming1.getReplaceable("y"), "b");
    printer.add(dp.makePrintableWith(renaming));
    assertTrue(printer.toString().equals("eval(a, b) ➡ eval(x - 1, y) | x > z { y }"));
  }
}

