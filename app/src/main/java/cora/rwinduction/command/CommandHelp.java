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

/** The environment command :help, which provides general of command-specific help. */
public class CommandHelp extends Command {
  private CmdList _clist;

  /** Set up the command, using the given command list to query information from. */
  public CommandHelp(CmdList lst) {
    _clist = lst;
  }

  public String queryName() {
    return ":help";
  }

  public FixedList<String> callDescriptor() {
    return FixedList.of(":help", ":help commands", ":help <command>");
  }

  public String helpDescriptor() {
    return "Prints a short description to explain how the prover works.";
  }

  protected boolean run(String args) {
    if (args.indexOf(' ') != -1) return failure("Too many arguments: :help takes 0 or 1");
    if (args.equals("")) return printGeneralHelp();
    if (args.equals("commands")) return printCommandList();
    Command cmd = _clist.queryCommand(args);
    if (cmd == null) return failure("Unknown command: " + args);
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
    TreeSet<String> env = new TreeSet<String>();
    TreeSet<String> deduction = new TreeSet<String>();
    for (String str : _clist.queryCommands()) {
      if (str.charAt(0) == ':') env.add(str);
      else deduction.add(str);
    }
    _module.println("You can use the following commands to interact with the prover:");
    StringBuilder envcmds = new StringBuilder();
    for (String m : env) envcmds.append(m + " ");
    StringBuilder deducmds = new StringBuilder();
    for (String d : deduction) deducmds.append(d + " ");
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

