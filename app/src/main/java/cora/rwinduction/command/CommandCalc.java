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

import java.util.ArrayList;
import java.util.Optional;

import charlie.exceptions.CustomParserException;
import charlie.util.FixedList;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.deduction.DeductionCalc;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command calc. */
public class CommandCalc extends Command {
  @Override
  public String queryName() {
    return "calc";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("calc <position_1> ... <position_n>");
  }
  
  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to rewrite the current equation with one or more " +
           "applications of a calculation step, in some subterm of the left- or right-hand " +
           "side of the equation.  You should supply at least one position, and at each position " +
           "either a value will be computed, an existing variable in the right-hand side, or a " +
           "fresh variable that will be added to the constraint.";
  }

  protected boolean run(CommandParsingStatus input) {
    Optional<DeductionCalc> step = createStep(input);
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, Optional.of(_module));
  }

  /** Main functionality of run, separated out for the sake of unit testing. */
  Optional<DeductionCalc> createStep(CommandParsingStatus input) {
    ArrayList<EquationPosition> posses = new ArrayList<EquationPosition>();
    String word = input.nextWord();
    try {
      while (word != null) {
        posses.add(EquationPosition.parse(word));
        word = input.nextWord();
      }
    }
    catch (CustomParserException e) {
      _module.println("Illegal position %a: %a", word, e.getMessage());
      return Optional.empty();
    }

    if (posses.size() == 0) {
      _module.println("Calc must be given at least one argument.");
      return Optional.empty();
    }
    
    return DeductionCalc.createStep(_proof, Optional.of(_module), posses);
  }
}

