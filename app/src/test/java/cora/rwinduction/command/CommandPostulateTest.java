/**************************************************************************************************
 Copyright 2025 Cynthia Kop

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
import java.util.ArrayList;
import java.util.Optional;
import java.util.Set;

import charlie.util.FixedList;
import charlie.terms.Renaming;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.deduction.DeductionPostulate;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;

class CommandPostulateTest {
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

  private TRS trs = setupTRS();

  @Test
  public void testCorrectEquationWithoutConstraint() {
    CommandPostulate cmd = new CommandPostulate();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof proof = new PartialProof(trs, EquationParser.parseEquationList(
        "sum1(x) = add(y, sum2(z))", trs), lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus("postulate sum1(x) = sum2(x)");
    status.nextWord();
    assertTrue(cmd.run(status));
    assertTrue(module.toString().equals(""));
    assertTrue(proof.getProofState().getEquations().size() == 2);
    assertTrue(proof.getProofState().getTopEquation().toString().equals(
      "E2: (• , sum1(x) ≈ sum2(x) , •)"));
    assertTrue(status.done());
  }

  @Test
  public void testCorrectEquationWithConstraint() {
    CommandPostulate cmd = new CommandPostulate();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof proof = new PartialProof(trs, EquationParser.parseEquationList(
        "sum1(x) = add(y, sum2(z))", trs), lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(
      "postulate iter(x, y, z) -><- iter(z, yy, x) | x + z = y ∧ yy = y + 1 ; delete");
    status.nextWord();
    assertTrue(cmd.run(status));
    assertTrue(module.toString().equals(""));
    assertTrue(proof.getProofState().getEquations().size() == 2);
    assertTrue(proof.getProofState().getTopEquation().toString().equals(
      "E2: (• , iter(x, y, z) ≈ iter(z, yy, x) | x + z = y ∧ yy = y + 1 , •)"));
    assertTrue(status.commandEnded());
    assertTrue(status.skipSeparator());
    assertTrue(status.nextWord().equals("delete"));
  }

  @Test
  public void testIncorrectEquation() {
    CommandPostulate cmd = new CommandPostulate();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof proof = new PartialProof(trs, EquationParser.parseEquationList(
        "sum1(x) = add(y, sum2(z))", trs), lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus(
      "postulate iter(x, y, z) ->< iter(z, yy, x) | x + z = y ∧ yy = y + 1 ; delete");
    status.nextWord();
    assertFalse(cmd.run(status));
    assertTrue(module.toString().equals("Parsing error: Unexpected equation: I expected a form " +
      "\"a -><- b (| c)?\" but only found @(iter, [x, y, z]).\n\n"));
    assertTrue(status.currentPosition() == 11);
    Renaming renaming = new Renaming(java.util.Set.of());
    assertTrue(status.readTerm(trs, renaming, module) != null);
  }

  @Test
  public void testTypeError() {
    CommandPostulate cmd = new CommandPostulate();
    OutputModule module = OutputModule.createUnicodeModule(trs);
    PartialProof proof = new PartialProof(trs, EquationParser.parseEquationList(
        "sum1(x) = add(y, sum2(z))", trs), lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandParsingStatus status = new CommandParsingStatus("postulate sum1(x) -><- x + 12 | x > 0");
    status.nextWord();
    assertFalse(cmd.run(status));
    assertTrue(module.toString().equals("Parsing error: Left-hand side of equation (sum1(x)) has " +
      "type Int while right-hand side (x + 12) has type Int!\n\n"));
    assertTrue(status.currentPosition() == 11);
  }
}

