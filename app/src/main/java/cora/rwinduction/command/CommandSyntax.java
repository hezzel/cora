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

import charlie.util.FixedList;
import cora.rwinduction.parser.CommandParsingStatus;

/** The environment command :syntax, which provides invocation information for a given command. */
public class CommandSyntax extends Command {
  private CmdList _clist;

  /** Set up the command, using the given command list to query information from. */
  public CommandSyntax(CmdList lst) {
    _clist = lst;
  }

  @Override
  public String queryName() {
    return ":syntax";
  }

  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of(":syntax <command>");
  }

  @Override
  public String helpDescriptor() {
    return "Query the ways to invoke a given command.";
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    String cmdname = input.nextWord();
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: :syntax takes at most 1 argument.",
                      input.currentPosition());
    }
    Command cmd = cmdname == null ? this : _clist.queryCommand(cmdname);
    if (cmd == null) return failure("Unknown command: " + cmdname);
    _module.println("Syntax for the command %a:", cmd.queryName());
    _module.startTable();
    for (String str : cmd.callDescriptor()) _module.println("%a", str);
    _module.endTable();
    return true;
  }
}

