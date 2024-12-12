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
import charlie.terms.Term;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.command.Command;
import cora.rwinduction.command.CmdMetaRules;

/** The syntax for the :rules meta command. */
public class SyntaxMetaRules extends Syntax {
  private TRS _trs;

  public SyntaxMetaRules(TRS trs) {
    _trs = trs;
  }

  public String queryName() {
    return ":rules";
  }

  public FixedList<String> callDescriptor() {
    return FixedList.of(":rules", ":rules <function symbol>");
  }

  public String helpDescriptor() {
    return "List all the rules available in the original TRS.  " +
           "You can also list only the rules with a specific root symbol.";
  }

  public Either<String,Command> parse(String str) {
    if (str.indexOf(' ') != -1) return makeEither("Too many arguments: :rules takes 0 or 1");
    if (str.equals("")) return makeEither(new CmdMetaRules());
    try {
      Term fterm = CoraInputReader.readTerm(str, _trs);
      if (fterm.isConstant()) return makeEither(new CmdMetaRules(fterm.queryRoot(), str));
      return makeEither("Argument to :rules should be a single function symbol");
    }
    catch (Exception e) { return makeEither(e.getMessage().trim()); }
  }
}

