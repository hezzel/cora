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

import java.util.TreeSet;
import charlie.util.FixedList;
import cora.io.OutputModule;

/** The environment command ":syntax", that describes the syntax of a specific command. */
public class CommandHelp extends EnvironmentCommand {
  private enum Kind { Plain, Commands, SingleCommand }
  private Kind _kind;
  private String _strInfo;
  private FixedList<String> _args;

  /** Creates the pure :help command. */
  public CommandHelp() {
    _kind = Kind.Plain;
    _strInfo = null;
    _args = null;
  }

  /** Creates the ":help commands" command, with the given list of commands. */
  public CommandHelp(FixedList<String> commands) {
    _kind = Kind.Commands;
    _strInfo = null;
    _args = commands;
  }

  /** Creates the :help <command> version of the command. */
  public CommandHelp(String name, String explanation, FixedList<String> syntaxes) {
    _kind = Kind.SingleCommand;
    _strInfo = name + ": " + explanation;
    _args = syntaxes;
  }

  public void run(OutputModule module) {
    switch (_kind) {
      case Plain: printGeneralHelp(module); break;
      case Commands: printCommandList(module); break;
      case SingleCommand: printCommandHelp(module); break;
    }
  }

  private void printGeneralHelp(OutputModule module) {
    module.println("Welcome to the interactive equivalence prover!");
    module.startTable();
    module.println("To list available commands, use: :help commands");
    module.println("To get out of the prover, use    :quit");
    module.endTable();
  }

  private void printCommandList(OutputModule module) {
    TreeSet<String> meta = new TreeSet<String>();
    TreeSet<String> deduction = new TreeSet<String>();
    for (String str : _args) {
      if (str.charAt(0) == ':') meta.add(str);
      else deduction.add(str);
    }
    module.println("You can use the following commands to interact with the prover:");
    StringBuilder metacmds = new StringBuilder();
    for (String m : meta) metacmds.append(m + " ");
    StringBuilder deducmds = new StringBuilder();
    for (String d : deduction) deducmds.append(d + " ");
    module.startTable();
    module.println("Prover commands: %a", metacmds.toString());
    module.println("Deduction rules: %a", deducmds.toString());
    module.endTable();
  }

  private void printCommandHelp(OutputModule module) {
    module.println(_strInfo);
    module.startTable();
    for (String str : _args) module.println("%a", str);
    module.endTable();
  }
}

