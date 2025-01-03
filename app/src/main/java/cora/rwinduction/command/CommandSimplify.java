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

import java.util.Optional;

import charlie.exceptions.CustomParserException;
import charlie.util.FixedList;
import charlie.terms.Renaming;
import charlie.terms.Substitution;
import charlie.terms.TermFactory;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.deduction.DeductionSimplify;
import cora.rwinduction.parser.CommandParsingStatus;

/** The syntax for the deduction command simplify. */
public class CommandSimplify extends Command {
  @Override
  public String queryName() {
    return "simplify";
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("simplify <rule>",
                        "simplify <rule> <position>",
                        "simplify <rule> with <substitution>",
                        "simplify <rule> <position> with <substitution>");
  }
  
  @Override
  public String helpDescriptor() {
    return "Use this deduction rule to rewrite the current equation with one of the known rules, " +
           "which might apply to some subterm of the left- or right-hand side of the equation.  " +
           "Note that rule names can be found using :rules, and positions have the form " +
           "L.<position> or R.<position>.  To simplify with a calculation rule, use the calc " +
           "command instead.";
  }

  protected boolean run(CommandParsingStatus input) {
    Optional<DeductionSimplify> step = createStep(input);
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, Optional.of(_module));
  }

  /** Main functionality of run, separated out for the sake of unit testing. */
  Optional<DeductionSimplify> createStep(CommandParsingStatus input) {
    // get ruleName (which is a valid rule)
    String ruleName = readRuleName(input);
    if (ruleName == null) return Optional.empty();

    // get position (a valid equation position)
    String arg = input.nextWord();
    EquationPosition pos = readEquationPos(arg);
    if (pos == null) return Optional.empty();

    // get substitution
    Substitution subst;
    if (arg != null && !arg.equals("with")) arg = input.nextWord();
    if (arg == null) subst = TermFactory.createEmptySubstitution();
    else if (!arg.equals("with")) {
      _module.println("Unexpected argument at position %a: expected \"with\" or end of command, " +
        "but got %a.", input.previousPosition(), arg);
      return Optional.empty();
    }
    else {
      subst = readSubstitution(input, ruleName);
      if (subst == null) return Optional.empty();
    }

    // we should end after this
    if (!input.commandEnded()) {
      _module.println("Unexpected argument at position %a: expected end of command.",
        input.currentPosition());
      return Optional.empty();
    }

    return DeductionSimplify.createStep(_proof, Optional.of(_module), ruleName, pos, subst);
  }

  /**
   * Helper function for run / createStep: this reads an identifier from the input, checks that
   * it's a valid rule, and if so, returns it.  If not, an error message is printed and null is
   * returned.
   */
  private String readRuleName(CommandParsingStatus input) {
    String txt = input.nextWord();
    if (txt != null && _proof.getContext().hasRule(txt)) return txt;
    if (txt == null) _module.println("Simplify should be invoked with at least 1 argument.");
    else _module.println("No such rule: " + txt);
    return null;
  }

  /**
   * Helper function for run / createStep: this parses the given string as an equation position --
   * provided it is not "with" -- and returns the result.  If reading fails, then null is returned
   * and an appropriate error message printed.
   * If input is null or "with", then the default position (TOPLEFT) is returned.
   */
  private EquationPosition readEquationPos(String input) {
    if (input == null || input.equals("with")) return EquationPosition.TOPLEFT;
    try {
      EquationPosition ret = EquationPosition.parse(input);
      if (ret != null) return ret;
      _module.println("Unexpected argument %a: I expected a valid position " +
        "(or \"with\").\n\n", input);
    }
    catch (CustomParserException e) {
      _module.println("Illegal position %a: %a", input, e);
    }
    return null;
  }

  /**
   * Given that CommandParsingStatus *should* point to the start of a substitution, parses and
   * returns the substitution, or prints an error message and returns null.
   */
  private Substitution readSubstitution(CommandParsingStatus input, String ruleName) {
    if (_proof.getProofState().isFinalState()) {
      _module.println("The proof state is empty; there is nothing to simplify.");
      return null;
    }
    Renaming keyNames = _proof.getContext().getRenaming(ruleName);
    Renaming valueNames = _proof.getProofState().getTopEquation().getRenaming();
    return input.readSubstitution(_proof.getContext().getTRS(), keyNames, valueNames, _module);
  }
}

