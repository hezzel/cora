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
import charlie.exceptions.ParseException;
import charlie.util.FixedList;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingStatus;
import charlie.parser.CoraTokenData;
import charlie.terms.Renaming;
import charlie.terms.Substitution;
import charlie.terms.TermFactory;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.deduction.DeductionSimplify;
import cora.rwinduction.parser.EquationPositionParser;
import cora.rwinduction.parser.SubstitutionParser;

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

  /** Main functionality of run, separated out for the sake of unit testing. */
  Optional<DeductionSimplify> createStep(ParsingStatus status) {
    // get ruleName (which is a valid rule)
    String ruleName = readRuleName(status);
    if (ruleName == null) return Optional.empty();

    // get position (a valid equation position)
    EquationPosition pos = readEquationPos(status);
    if (pos == null) return Optional.empty();

    // get substitution
    Substitution subst = readSubstitution(status, ruleName);
    if (subst == null) return Optional.empty();

    return DeductionSimplify.createStep(_proof, Optional.of(_module), ruleName, pos, subst);
  }

  protected boolean run(ParsingStatus status) {
    Optional<DeductionSimplify> step = createStep(status);
    if (step.isEmpty()) return false;
    return step.get().verifyAndExecute(_proof, Optional.of(_module));
  }

  /**
   * Helper function for run: this reads an identifier from the parsing status, checks that it's a
   * valid rule, and if so, returns it.  If not, either a ParseException is thrown or an error
   * message printed and null returned.
   */
  private String readRuleName(ParsingStatus status) {
    Token tok = status.expect(CoraTokenData.IDENTIFIER, "a rule name");
    if (tok == null) return null;
    String txt = tok.getText();
    if (_proof.getContext().hasRule(txt)) return txt;
    _module.println("Nu such rule: " + txt);
    return null;
  }

  /**
   * Helper function for run: this reads an equation position from the given parsing status, parses
   * it into an EquationPosition type, and returns the result.  If reading fails, then null is
   * returned and an appropriate error message given (or: a ParseException).
   * If no position is given, then the default position (TOPLEFT) is returned.
   */
  private EquationPosition readEquationPos(ParsingStatus status) {
    if (status.peekNext().getText().equals("with") || commandEnds(status)) {
      return EquationPosition.TOPLEFT;
    }
    try {
      EquationPosition ret = EquationPositionParser.readPosition(status);
      if (ret == null) {
        status.storeError("Unexpected argument: expected a valid position (or \"with\").",
                          status.peekNext());
      }
      return ret;
    }
    catch (CustomParserException e) {
      _module.println("%a", e);
      return null;
    }
  }

  private Substitution readSubstitution(ParsingStatus status, String ruleName) {
    if (commandEnds(status)) return TermFactory.createEmptySubstitution();
    Token tok = status.expect(CoraTokenData.IDENTIFIER, "\"with\" or end of command");
    if (tok == null) return null;
    if (!tok.getText().equals("with")) {
      status.storeError("Expected \"with\" or end of command, but got \"" + tok.getText() +
        "\"", tok);
      return null;
    }
    if (_proof.getProofState().isFinalState()) {
      _module.println("The proof state is empty; there is nothing to simplify.");
      return null;
    }
    Renaming keyNames = _proof.getContext().getRenaming(ruleName);
    Renaming valueNames = _proof.getProofState().getTopEquation().getRenaming();
    return SubstitutionParser.parseSubstitution(status, _proof.getContext().getTRS(),
                                                keyNames, valueNames);
  }
}

