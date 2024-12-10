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

import java.util.HashMap;
import charlie.util.Either;
import cora.rwinduction.engine.Command;

public class CommandParser {
  private HashMap<String,Syntax> _syntaxes;

  public CommandParser() {
    _syntaxes = new HashMap<String,Syntax>();
  }

  public void registerSyntax(String name, Syntax syntax) {
    _syntaxes.put(name, syntax);
  }

  public Either<String,Command> parse(String str) {
    String cmd, rest;
    str = str.trim();
    int c = str.indexOf(' ');
    if (c == -1) { cmd = str; rest = ""; }
    else { cmd = str.substring(0, c); rest = str.substring(c+1).trim(); }
    if (!_syntaxes.containsKey(cmd)) {
      return new Either.Left<String,Command>("Unknown command: " + cmd + ".  " +
        "Use \":help commands\" to list available commands.");
    }
    return _syntaxes.get(cmd).parse(rest);
  }
}

