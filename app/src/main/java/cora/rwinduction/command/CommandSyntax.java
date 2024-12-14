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

/** The environment command :syntax, which provides invocation information for a given command. */
public class CommandSyntax extends Command {
  private CmdList _clist;

  /** Set up the command, using the given command list to query information from. */
  public CommandSyntax(CmdList lst) {
    _clist = lst;
  }

  public String queryName() {
    return ":syntax";
  }

  public FixedList<String> callDescriptor() {
    return FixedList.of(":syntax <command>");
  }

  public String helpDescriptor() {
    return "Query the ways to invoke a given command.";
  }

  protected boolean run(String args) {
    if (args.indexOf(' ') != -1) return failure("Too many arguments: :syntax takes 0 or 1");
    Command cmd = args.equals("") ? this : _clist.queryCommand(args);
    if (cmd == null) return failure("Unknown command: " + args);
    _module.println("Syntax for the command %a:", cmd.queryName());
    _module.startTable();
    for (String str : cmd.callDescriptor()) _module.println("%a", str);
    _module.endTable();
    return true;
  }
}

