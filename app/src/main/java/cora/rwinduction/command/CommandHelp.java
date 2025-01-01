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

import java.util.TreeSet;
import charlie.util.FixedList;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingStatus;
import charlie.parser.CoraTokenData;
import cora.rwinduction.parser.CommandParser;

/** The environment command :help, which provides general of command-specific help. */
public class CommandHelp extends Command {
  private CmdList _clist;

  /** Set up the command, using the given command list to query information from. */
  public CommandHelp(CmdList lst) {
    _clist = lst;
  }

  @Override
  public String queryName() {
    return ":help";
  }

  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of(":help", ":help commands", ":help <command>");
  }

  @Override
  public String helpDescriptor() {
    return "Prints a short description to explain how the prover works.";
  }

  protected boolean run(ParsingStatus status) {
    // syntax: :help
    if (commandEnds(status)) return printGeneralHelp();
    // syntax: :help commands
    if (status.peekNext().getName().equals(CoraTokenData.IDENTIFIER) &&
        status.peekNext().getText().equals("commands")) {
      status.nextToken();
      if (!commandEnds(status)) {
        status.storeError("Too many arguments to :help commands.", status.peekNext());
      }
      return printCommandList();
    }
    // syntax: :help command
    String txt = CommandParser.parseCommand(status);
    Command cmd = _clist.queryCommand(txt);
    if (cmd == null) return failure("Unknown command: " + txt);
    if (!commandEnds(status)) {
      status.storeError("Unexpected argument: :help takes at most 1.", status.peekNext());
    }
    return printCommandHelp(cmd);
  }

  /** Prints a general help message and returns true */
  private boolean printGeneralHelp() {
    _module.println("Welcome to the interactive equivalence prover!");
    _module.startTable();
    _module.println("To list available commands, use: :help commands");
    _module.println("To get out of the prover, use    :quit");
    _module.endTable();
    return true;
  }

  /** Prints a list of all commands to the underlying output module, and returns true */
  private boolean printCommandList() {
    _module.println("You can use the following commands to interact with the prover:");
    StringBuilder envcmds = new StringBuilder();
    StringBuilder deducmds = new StringBuilder();
    for (String str : _clist.queryCommands()) {
      if (str.charAt(0) == ':') envcmds.append(str + " ");
      else deducmds.append(str + " ");
    }
    _module.startTable();
    _module.println("Prover commands: %a", envcmds.toString());
    _module.println("Deduction rules: %a", deducmds.toString());
    _module.endTable();
    return true;
  }

  /** Prints a help description for the given command, and returns true */
  private boolean printCommandHelp(Command cmd) {
    _module.println(cmd.queryName() + ": " + cmd.helpDescriptor());
    _module.startTable();
    for (String str : cmd.callDescriptor()) _module.println("%a", str);
    _module.endTable();
    return true;
  }
}

