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

package cora.rwinduction.interactive;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;

import charlie.util.FixedList;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.Command;
import cora.rwinduction.parser.ExtendedTermParser;

class CommandHelpTest {
  private PartialProof createPP(OutputModule module) {
    TRS trs = CoraInputReader.readTrsFromString(
        "sum1 :: Int -> result\n" +
        "sum2 :: Int -> result\n");
    Equation eq = ExtendedTermParser.parseEquation("sum1(x) = sum2(x) | x ≥ 0", trs);
    return new PartialProof(trs, FixedList.of(eq), module.queryTermPrinter());
  }

  @Test
  public void testHelpPlain() {
    Command cmd = new CommandHelp();
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    cmd.run(createPP(module), module);
    assertTrue(module.toString().equals(
    "Welcome to the interactive equivalence prover!\n\n" +
    "  To list available commands, use: :help commands\n" +
    "  To get out of the prover, use    :quit\n\n"));
  }

  @Test
  public void testHelpCommands() {
    Command cmd = new CommandHelp(FixedList.of(":quit", ":rules", "simplify", "delete", ":help"));
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    cmd.run(createPP(module), module);
    assertTrue(module.toString().equals(
      "You can use the following commands to interact with the prover:\n\n" +
      "  Prover commands: :help :quit :rules \n" +
      "  Deduction rules: delete simplify \n\n"));
  }

  @Test
  public void testHelpSingle() {
    Command cmd = new CommandHelp(":rules", "haha", FixedList.of(":rules", ":rules arg"));
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    cmd.run(createPP(module), module);
    assertTrue(module.toString().equals(
      ":rules: haha\n\n" +
      "  :rules\n" +
      "  :rules arg\n\n"));
  }
}

