/**************************************************************************************************
 Copyright 2025 Cynthia Kop

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
import java.util.Optional;

import charlie.exceptions.ParseException;
import charlie.util.FixedList;
import charlie.util.Pair;
import charlie.terms.Renaming;
import charlie.trs.TRS;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.deduction.DeductionPostulate;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.parser.EquationParser;

/** The syntax for the deduction command postulate. */
public class CommandPostulate extends Command {
  @Override
  public String queryName() {
    return "postulate";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("postulate <equation>");
  }
  
  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to introduce a new equation into the set of goals.";
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    TRS trs = _proof.getContext().getTRS();
    Pair<Equation,Renaming> pair = input.readEquation(trs, _module);
    if (pair == null) return false;
    Optional<DeductionPostulate> ostep =
      DeductionPostulate.createStep(_proof, Optional.of(_module), pair.fst(), pair.snd());
    if (ostep.isEmpty()) return false;
    return ostep.get().verifyAndExecute(_proof, Optional.of(_module));
  }

  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    ret.add(new TabSuggestion(null, "equation"));
    return ret;

  }
}

