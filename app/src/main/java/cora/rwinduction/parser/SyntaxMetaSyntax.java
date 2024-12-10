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

package cora.rwinduction.parser;

import charlie.util.Either;
import charlie.util.FixedList;
import cora.rwinduction.command.Command;
import cora.rwinduction.command.CmdMetaSyntax;

/** The syntax for the :syntax meta command. */
public class SyntaxMetaSyntax extends Syntax {
  private CommandParser _cparse;

  /**
   * Creates the Syntax for the syntax command, taking its commands from the given command parser.
   */
  public SyntaxMetaSyntax(CommandParser cp) {
    _cparse = cp;
  }

  public String queryName() {
    return ":syntax";
  }

  public FixedList<String> callDescriptor() {
    return FixedList.of(":syntax", ":syntax <command>");
  }

  public Either<String,Command> parse(String str) {
    if (str.indexOf(' ') != -1) return makeEither("Too many arguments: :syntax takes 0 or 1");
    Syntax cmd = str.equals("") ? this : _cparse.querySyntax(str);
    if (cmd == null) return makeEither("Unknown command: " + str);
    return makeEither(new CmdMetaSyntax(cmd.queryName(), cmd.callDescriptor()));
  }
}

