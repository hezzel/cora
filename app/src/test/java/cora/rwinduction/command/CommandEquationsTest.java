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
import java.util.Set;

import charlie.parser.lib.ParsingStatus;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.parser.EquationParser;

class CommandEquationsTest {
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

  private boolean runCommand(OutputModule module, String str) {
    CommandEquations cmd = new CommandEquations();
    CommandInduct induct = new CommandInduct();
    TRS trs = setupTRS();
    PartialProof proof = new PartialProof(trs, EquationParser.parseEquationList(
      "sum1(x) = sum2(x) | x ≥ 0 ; error = return(3)", trs),
      lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    induct.storeContext(proof, module);
    induct.execute(new CommandParsingStatus(""));
    CommandParsingStatus status = new CommandParsingStatus(str);
    status.nextWord(); // :equations
    return cmd.execute(status);
  }

  @Test
  public void testPrintBasic() {
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(runCommand(module, ":equations"));
    assertTrue(module.toString().equals(
      "  E1: sum1(x) ≈ sum2(x) | x ≥ 0\n" +
      "  E3: error ≈ return(3)\n\n"));
  }

  @Test
  public void testPrintFull() {
    OutputModule module = OutputModule.createUnitTestModule();
    assertTrue(runCommand(module, ":equations full"));
    assertTrue(module.toString().equals(
      "  E1: (• , sum1(x) ≈ sum2(x) | x ≥ 0 , •)\n" +
      "  E3: (error , error ≈ return(3) , return(3))\n\n"));
  }
}

