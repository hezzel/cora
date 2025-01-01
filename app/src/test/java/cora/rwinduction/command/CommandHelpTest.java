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
import charlie.parser.lib.ParsingStatus;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.RWParser;
import cora.rwinduction.parser.EquationParser;

class CommandHelpTest {
  private PartialProof createPP(OutputModule module) {
    TRS trs = CoraInputReader.readTrsFromString(
        "sum1 :: Int -> result\n" +
        "sum2 :: Int -> result\n");
    return new PartialProof(trs,
      EquationParser.parseEquationList("sum1(x) = sum2(x) | x ≥ 0", trs),
      module.queryTermPrinter());
  }

  private CmdList makeCmdList() {
    CmdList lst = new CmdList();
    lst.registerCommand(new CommandQuit());
    lst.registerCommand(new CommandRules());
    lst.registerCommand(new CommandDelete());
    lst.registerCommand(new CommandHelp(lst));
    return lst;
  }

  private boolean runCommand(OutputModule module, String str) {
    CommandHelp cmd = new CommandHelp(makeCmdList());
    PartialProof pp = createPP(module);
    cmd.storeContext(pp, module);
    ParsingStatus status = RWParser.createStatus(str);
    status.nextToken(); // :
    status.nextToken(); // help
    boolean ret = cmd.execute(status);
    assertTrue(status.nextToken().isEof());
    return ret;
  }

  @Test
  public void testHelpPlain() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    runCommand(module, ":help");
    assertTrue(module.toString().equals(
    "Welcome to the interactive equivalence prover!\n\n" +
    "  To list available commands, use: :help commands\n" +
    "  To get out of the prover, use    :quit\n\n"));
  }

  @Test
  public void testHelpCommands() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    runCommand(module, ": help   commands");
    assertTrue(module.toString().equals(
      "You can use the following commands to interact with the prover:\n\n" +
      "  Prover commands: :help :quit :rules \n" +
      "  Deduction rules: delete \n\n"));
  }

  @Test
  public void testHelpSingle() {
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    runCommand(module, ":help : help");
    assertTrue(module.toString().equals(
      ":help: Prints a short description to explain how the prover works.\n\n" +
      "  :help\n" +
      "  :help commands\n" +
      "  :help <command>\n\n"));
  }

  @Test
  public void testBadInvocation() {
    Command cmd = new CommandHelp(makeCmdList());
    assertThrows(RuntimeException.class, () ->
      cmd.execute(RWParser.createStatus(":help")));
    OutputModule module = DefaultOutputModule.createUnicodeModule();
    cmd.storeContext(createPP(module), module);
    assertFalse(cmd.execute(RWParser.createStatus("quit")));
    assertTrue(module.toString().equals("Unknown command: quit\n\n"));
    module.clear();
    assertFalse(cmd.execute(RWParser.createStatus(":quit :help")));
    assertTrue(module.toString().equals(
      "Parse error at 1:7: Unexpected argument: :help takes at most 1.\n\n"));
  }
}

