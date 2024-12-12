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
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.ProverContext;
import cora.rwinduction.parser.ExtendedTermParser;

class CmdMetaHelpTest {
  /* If we want to do it neatly we can build a ProverContext, but the command doesn't really need
     one, as it shouldn't be using the ProverContext.
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "sum1 :: Int -> result\n" +
      "sum2 :: Int -> result\n");
  }

  private ProverContext createContext(TRS trs, OutputModule module) {
    Equation eq = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x ≥ 0", trs);
    return new ProverContext(trs, FixedList.of(eq), module.queryTermPrinter());
  }
  */

  @Test
  public void testHelpPlain() {
    Command cmd = new CmdMetaHelp();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    cmd.run(null, module);
    assertTrue(module.toString().equals(
    "Welcome to the interactive equivalence prover!\n\n" +
    "  To list available commands, use: :help commands\n" +
    "  To get out of the prover, use    :quit\n\n"));
  }

  @Test
  public void testHelpCommands() {
    Command cmd = new CmdMetaHelp(FixedList.of(":quit", ":rules", "simplify", "delete", ":help"));
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    cmd.run(null, module);
    assertTrue(module.toString().equals(
      "You can use the following commands to interact with the prover:\n\n" +
      "  Prover commands: :help :quit :rules \n" +
      "  Deduction rules: delete simplify \n\n"));
  }

  @Test
  public void testHelpSingle() {
    Command cmd = new CmdMetaHelp(":rules", "haha", FixedList.of(":rules", ":rules arg"));
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    cmd.run(null, module);
    assertTrue(module.toString().equals(
      ":rules: haha\n\n" +
      "  :rules\n" +
      "  :rules arg\n\n"));
  }
}

