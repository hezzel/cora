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

import charlie.exceptions.CustomParserException;
import charlie.util.Pair;
import charlie.util.FixedList;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.DeductionSimplify;

/** The syntax for the deduction command simplify. */
public class CommandSimplify extends Command {
  private DeductionSimplify _drule;

  public CommandSimplify() {
    _drule = null;
  }

  public String queryName() {
    return "simplify";
  }
  
  public FixedList<String> callDescriptor() {
    return FixedList.of("simplify <rule>",
                        "simplify <rule> <position>",
                        "simplify <rule> with <substitution>",
                        "simplify <rule> <position> with <substitution>");
  }
  
  public String helpDescriptor() {
    return "Use this deduction rule to rewrite the current equation with one of the known rules, " +
           "which might apply to some subterm of the left- or right-hand side of the equation.  " +
           "Note that rule names can be found using :rules, and positions have the form " +
           "L.<position> or R.<position>.  To simplify with a calculation rule, use the calc " +
           "command instead.";
  }
  
  protected boolean run(String args) {
    String ruleName;
    String posString;
    String subString;

    Pair<String,String> p = splitWord(args);
    ruleName = p.fst();
    p = splitWord(p.snd());
    if (p.fst().equals("with")) {
      posString = "";
      subString = p.snd();
    }
    else {
      posString = p.fst();
      p = splitWord(p.snd());
      if (p.fst().equals("with")) subString = p.snd();
      else if (!p.fst().equals("")) return failure("Unexpected string: " + p.fst());
    }

    // check rulename
    if (ruleName.equals("")) return failure("Simplify requires at least one argument.");
    if (!_proof.hasRule(ruleName)) return failure("No such rule: " + ruleName);
    
    // read position
    EquationPosition pos = null;
    try { pos = EquationPosition.parse(posString); }
    catch (CustomParserException e) {
      return failure("Could not parse position " + posString + ": " + e.getMessage());
    }
    
    // TODO: substitution (and function refactoring)

    // run the simplify command with appropriate arguments
    if (_drule == null) _drule = new DeductionSimplify(_proof, _module);
    return _drule.apply(ruleName, pos);
  }
}

