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
import cora.rwinduction.command.CmdMetaQuit;

/** The syntax for the :quit meta command. */
public class SyntaxMetaQuit extends Syntax {
  public String queryName() { return ":quit"; }
  public FixedList<String> callDescriptor() { return FixedList.of(":quit"); }
  public String helpDescriptor() {
    return "Use this to abort the interactive prover process.  " +
           "Note that your result will not be saved!";
  }
  public Either<String,Command> parse(String str) {
    if (str.equals("")) return makeEither(new CmdMetaQuit());
    else return makeEither(":quit should be invoked without arguments");
  }
}

