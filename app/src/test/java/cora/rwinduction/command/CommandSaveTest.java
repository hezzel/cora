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
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;

class CommandSaveTest {
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

  private CommandSave setupCommand(OutputModule module) {
    CommandSave cmd = new CommandSave();
    FixedList<EquationContext> ecs =
      EquationParser.parseEquationList("sum1(x) = add(y,sum2(z)) | z ≥ y ; " +
                                       "sum2(z) = sum1(z)", trs);
    PartialProof proof = new PartialProof(trs, ecs,
                                          lst -> module.generateUniqueNaming(lst));
    cmd.storeContext(proof, module);
    CommandInduct induct = new CommandInduct();
    induct.storeContext(proof, module);
    induct.run(new CommandParsingStatus(""));
    CommandCase ccase = new CommandCase();
    ccase.storeContext(proof, module);
    ccase.run(new CommandParsingStatus("z > 0"));
    return cmd;
  }

  @Test
  public void testCommand() {
    OutputModule module = OutputModule.createUnicodeModule(trs);
    CommandSave cmd = setupCommand(module);
    String history = cmd.storeHistory();
    String sep = System.lineSeparator();
    assertTrue(history.equals(
      "GOAL E1: (* , sum1(x) [=] add(y, sum2(z)) | z >= y , *)" + sep +
      "GOAL E2: (* , sum2(z) [=] sum1(z) , *)" + sep +
      "induct" + sep +
      "case z > 0" + sep));
  }
}

