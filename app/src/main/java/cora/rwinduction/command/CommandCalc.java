/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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

import charlie.util.FixedList;
import charlie.terms.position.PositionFormatException;
import charlie.terms.Term;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.deduction.DeductionCalc;
import cora.rwinduction.engine.deduction.DeductionCalcAll;
import cora.rwinduction.engine.deduction.DeductionCalcAll.Side;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command calc. */
public class CommandCalc extends DeductionCommand {
  @Override
  public String queryName() {
    return "calc";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("calc", "calc left", "calc right", "calc <position_1> ... <position_n>");
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule to rewrite the current equation with one or more " +
      "applications of a calculation step, in some subterm of the left- or right-hand side of " +
      "the equation.");
    module.println("Invoking this command without arguments causes all possible calculations to " +
      "be performed immediately.  Specifying \"left\" or \"right\" does only calculations on the " +
      "given side.  Alternatively, you can supply one or more positions.");
    module.println("For each calculatable position, either a value will be computed, or an " +
      "existing variable in the constraint, or a fresh variable that is then added to the " +
      "constraint.  Note that, unless you specify positions, the calculations will always be " +
      "done outermost-first; e.g., x + (y + z) will be replaced by a single variable (defined " +
      "in the constraint to be x + (y + z)); there will not be variable a = x + b and b = y + z.");
  }

  @Override
  protected DeductionStep createStep(CommandParsingStatus input) {
    String word = input.nextWord();
    Optional<OutputModule> o = optionalModule();
    if (word == null) return DeductionCalcAll.createStep(_proof, o, Side.Both);
    if (word.equals("left")) return DeductionCalcAll.createStep(_proof, o, Side.Left);
    if (word.equals("right")) return DeductionCalcAll.createStep(_proof, o, Side.Right);
    return createPositionStep(input, word);
  }

  /**
   * If the user has supplied arguments other than left or right, they must be supplying positions!
   * Parse the positions, and create a calc <positions> command.
   */
  private DeductionCalc createPositionStep(CommandParsingStatus input, String word) {
    ArrayList<EquationPosition> posses = new ArrayList<EquationPosition>();
    try {
      while (word != null) {
        posses.add(EquationPosition.parse(word));
        word = input.nextWord();
      }
    }
    catch (PositionFormatException e) {
      _module.println("Illegal position %a (character %a): %a", word, e.queryProblemPos(),
        e.queryExplanation());
      return null;
    }
    
    return DeductionCalc.createStep(_proof, Optional.of(_module), posses);
  }

  /** Tab suggestions for this command are just the positions available to the user. */
  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    Equation equation = _proof.getProofState().getTopEquation().getEquation();
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    if (args.equals("")) {
      ret.add(new TabSuggestion("left", "keyword"));
      ret.add(new TabSuggestion("right", "keyword"));
    }
    addCalculatablePositions(equation.getLhs(), EquationPosition.Side.Left, ret);
    addCalculatablePositions(equation.getRhs(), EquationPosition.Side.Right, ret);
    ret.add(endOfCommandSuggestion());
    return ret;
  }

  /**
   * Helper function for suggestNext: this goes through all the positions in the given term, and
   * adds <side><pos> to the given suggestion list if the subterm of term at that position is
   * something that may be calculated.
   */
  private void addCalculatablePositions(Term term, EquationPosition.Side side,
                                        ArrayList<TabSuggestion> suggestions) {
    Printer printer = PrinterFactory.createParseablePrinter(_proof.getContext().getTRS());
    term.visitSubterms( (s,p) -> {
      if (s.isApplication() && s.isTheoryTerm() && s.isFirstOrder()) {
        EquationPosition pos = new EquationPosition(side, p);
        pos.print(printer);
        suggestions.add(new TabSuggestion(printer.toString(), "position"));
        printer.clear();
      }
    });
  }
}

