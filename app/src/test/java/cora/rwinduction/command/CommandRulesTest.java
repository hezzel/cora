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

package cora.rwinduction.command;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;

import charlie.util.FixedList;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.ExtendedTermParser;

class CommandRulesTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "return :: Int -> result\n" +
      "error :: result\n" +
      "sum1 :: Int -> result\n" +
      "sum1(x) -> return(0) | x <= 0\n" +
      "sum1(x) -> add(x,sum1(x-1)) | x > 0\n" +
      "add :: Int -> result -> result\n" +
      "add(x, return(y)) -> return(x+y)\n" +
      "add(x, error) -> error\n" +
      "sum2 :: Int -> result\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> result\n" +
      "iter(x, i, z) -> return(z) | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n");
  }

  private Command setupCommand(OutputModule module) {
    CommandRules cmd = new CommandRules();
    TRS trs = setupTRS();
    Equation eq = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x ≥ 0", trs);
    PartialProof proof = new PartialProof(trs, FixedList.of(eq), module.queryTermPrinter());
    cmd.storeContext(proof, module);
    return cmd;
  }

  @Test
  public void testPrintAll() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = setupCommand(module);
    assertTrue(cmd.execute(""));
    assertTrue(module.toString().equals(
      "  O1: sum1(x) → return(0) | x ≤ 0\n" +
      "  O2: sum1(x) → add(x, sum1(x - 1)) | x > 0\n" +
      "  O3: add(x, return(y)) → return(x + y)\n" +
      "  O4: add(x, error) → error\n" +
      "  O5: sum2(x) → iter(x, 0, 0)\n" +
      "  O6: iter(x, i, z) → return(z) | i > x\n" +
      "  O7: iter(x, i, z) → iter(x, i + 1, z + i) | i ≤ x\n\n"));
  }

  @Test
  public void testPrintConstructorSymbol() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = setupCommand(module);
    assertTrue(cmd.execute("return"));
    assertTrue(module.toString().equals("There are no rules with return as root symbol.\n\n"));
  }

  @Test
  public void testPrintDefinedSymbol() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = setupCommand(module);
    assertTrue(cmd.execute("iter"));
    assertTrue(module.toString().equals(
      "  O6: iter(x, i, z) → return(z) | i > x\n" +
      "  O7: iter(x, i, z) → iter(x, i + 1, z + i) | i ≤ x\n\n"));
  }

  @Test
  public void testPrintCalculationSymbol() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = setupCommand(module);
    assertTrue(cmd.execute("[=_Bool]"));
    assertTrue(module.toString().equals(
      "There are no rules with [⇔] as root symbol.\n\n" +
      "The calculation rule for this symbol is: x1 ⇔ x2 → z | z ⇔ (x1 ⇔ x2) .\n\n"));
  }

  @Test
  public void testParseTwoArguments() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = setupCommand(module);
    assertFalse(cmd.execute("sum +"));
    assertTrue(module.toString().equals("Too many arguments: :rules takes 0 or 1\n\n"));
  }

  @Test
  public void testParseUnknownArgument() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = setupCommand(module);
    assertFalse(cmd.execute("sum3"));
    assertTrue(module.toString().equals("1:1: Undeclared symbol: sum3.  " +
      "Type cannot easily be deduced from context.\n\n"));
  }

  @Test
  public void testParseUnknownCalculation() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    Command cmd = setupCommand(module);
    assertFalse(cmd.execute("[and]"));
    assertTrue(module.toString().equals("1:2: Expected infix symbol but got IDENTIFIER (and)\n\n"));
  }
}

