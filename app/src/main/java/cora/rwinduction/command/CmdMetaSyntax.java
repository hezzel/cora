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
import cora.io.OutputModule;
import cora.rwinduction.engine.ProverContext;

/** The syntax command, that describes the syntax of a specific command. */
public class CmdMetaSyntax implements Command {
  private String _commandName;
  private FixedList<String> _syntaxes;

  public CmdMetaSyntax(String name, FixedList<String> syntaxes) {
    _commandName = name;
    _syntaxes = syntaxes;
  }

  public void run(ProverContext context, OutputModule module) {
    module.println("Syntax for the command " + _commandName);
    module.startTable();
    for (String str : _syntaxes) module.println("%a", str);
    module.endTable();
  }
}

