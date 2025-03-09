/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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

import java.util.ArrayList;
import java.util.TreeSet;
import charlie.util.FixedList;
import cora.rwinduction.parser.CommandParsingStatus;

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

  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    ret.add(endOfCommandSuggestion());
    // if they already supplied an argument, we don't need to suggest another
    if (!args.equals("")) return ret;
    ret.add(new TabSuggestion("commands", "keyword"));
    for (String name : _clist.queryCommands()) ret.add(new TabSuggestion(name, "command"));
    return ret;
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    // syntax: :help
    if (input.commandEnded()) return printGeneralHelp();
    // if not 0 arguments, we must have exactly 1!
    String txt = input.nextWord();
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: :help takes at most 1 argument.",
                      input.currentPosition());
      return false;
    }
    // syntax: :help commands
    if (txt.equals("commands")) return printCommandList();
    // syntax: :help command
    Command cmd = _clist.queryCommand(txt);
    if (cmd == null) return failure("Unknown command: " + txt);
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

