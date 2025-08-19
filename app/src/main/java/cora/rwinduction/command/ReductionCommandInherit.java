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
import java.util.TreeSet;

import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.terms.position.PositionFormatException;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.parser.CommandParsingStatus;

/**
 * A base inherit for commands like Simplify and Hypothesis, which have a lot of shared
 * functionality.
 */
abstract class ReductionCommandInherit extends DeductionCommand {
  protected String _commandName;
  private String _reducibleKind;

  protected ReductionCommandInherit(String cmdName, String kind) {
    _commandName = cmdName;
    _reducibleKind = kind;
  }

  @Override
  public final String queryName() {
    return _commandName;
  }
  
  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of(_commandName + " " + _reducibleKind,
                        _commandName + " " + _reducibleKind + " <position>",
                        _commandName + " " + _reducibleKind + " with <substitution>",
                        _commandName + " " + _reducibleKind + " <position> with <substitution>");
  }

  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    TreeSet<FunctionSymbol> symbols = existingSymbols();
    String[] parts = args.split("\\s+");

    // no arguments => they haven't yet given the kind
    if (parts.length == 0 || parts[0].equals("")) {
      addTabSuggestionsForKind(symbols, ret);
      return ret;
    }

    Term left = getLeftFor(parts[0]);
    if (left == null) return ret;

    // just one argument: suggest a position, since omitting it just means the position L
    if (parts.length == 1) {
      storePositionSuggestions(left, ret, EquationPosition.Side.Left,
                               _proof.getProofState().getTopEquation().getEquation().getLhs());
      storePositionSuggestions(left, ret, EquationPosition.Side.Right,
                               _proof.getProofState().getTopEquation().getEquation().getRhs());
      return ret;
    }

    // 2 arguments! We suggest "with" if it's not already there, or suggest that they stop here.
    if (parts.length == 2 && !parts[1].equals("with")) {
      ret.add(new TabSuggestion("with", "keyword"));
      ret.add(endOfCommandSuggestion());
      return ret;
    }

    // if we've seen something other than with, it's buggy
    if (parts.length >= 3 && !parts[1].equals("with") && !parts[2].equals("with")) return ret;

    // there's a with! Anything after that is part of the substitution, unless we've just finished
    // the substitution
    String last = parts[parts.length-1];
    if (!last.equals("") && last.charAt(last.length()-1) == ']') ret.add(endOfCommandSuggestion());
    else ret.add(new TabSuggestion(null, "substitution"));

    return ret;
  }

  /** Helper for suggestNext: returns the function symbols occurring in the top equation. */
  private TreeSet<FunctionSymbol> existingSymbols() {
    TreeSet<FunctionSymbol> ret = new TreeSet<FunctionSymbol>();
    if (_proof.getProofState().isFinalState()) return ret;
    Equation eq = _proof.getProofState().getTopEquation().getEquation();
    eq.getLhs().storeFunctionSymbols(ret);
    eq.getRhs().storeFunctionSymbols(ret);
    return ret;
  }

  /**
   * Helper function for suggestNext: this suggests the options for the first argument, provided
   * that the only symbols occurring in the top equation are in occurringSymbols.
   */
  protected abstract void addTabSuggestionsForKind(TreeSet<FunctionSymbol> occuringSymbols,
                                                   ArrayList<TabSuggestion> suggestions);
  
  /**
   * Helper function for suggestNext: this provides the left-hand side of the rule, induction
   * hypothesis or whatever that is defined by the given name.  If there is no such thing, then
   * null is returned instead.
   */
  protected abstract Term getLeftFor(String kindName);

  /**
   * Helper function for suggestNext: this adds to suggestions the positions within term (combined
   * with the given side) that may be reduced by a reducer whose left-hand side is leftOfReducer.
   */
  private void storePositionSuggestions(Term leftOfReducer, ArrayList<TabSuggestion> suggestions,
                                        EquationPosition.Side side, Term term) {
    Printer printer = PrinterFactory.createParseablePrinter(_proof.getContext().getTRS());
    term.visitSubterms( (s,p) -> {
      if (leftOfReducer.match(s) != null) {
        EquationPosition pos = new EquationPosition(side, p);
        pos.print(printer);
        suggestions.add(new TabSuggestion(printer.toString(), "position"));
        printer.clear();
      }
    });
  }

  /**
   * After having read COMMAND KIND, this function will read the rest of the input, which may or
   * may not include an equation position and a substitution, and return the results.
   *
   * If the input does not have the right shape, then an error message is printed and null returned.
   */
  protected Pair<EquationPosition,Substitution> readCommandRemainder(Renaming kindRenaming,
                                                                     CommandParsingStatus input) {
    String arg = input.nextWord();
    EquationPosition pos = readEquationPos(arg);
    if (pos == null) return null;

    Substitution subst;
    if (arg != null && !arg.equals("with")) arg = input.nextWord();
    if (arg == null) subst = TermFactory.createEmptySubstitution();
    else if (!arg.equals("with")) {
      _module.println("Unexpected argument at position %a: expected \"with\" or end of command, " +
        "but got %a.", input.previousPosition(), arg);
      return null;
    }
    else {
      subst = readSubstitution(input, kindRenaming);
      if (subst == null) return null;
    }
    
    // we should end after this
    if (!verifyEnded(input)) return null;

    return new Pair<EquationPosition,Substitution>(pos, subst);
  }

  /**
   * Helper function for readCommandRemainder: this parses the given string as an equation position
   * -- provided it is not "with" -- and returns the result.  If reading fails, then null is
   * returned and an appropriate error message printed.
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
    catch (PositionFormatException e) {
      _module.println("Illegal position %a (character %a): %a", input, e.queryProblemPos(),
        e.queryExplanation());
    }
    return null;
  }

  /**
   * Given that CommandParsingStatus *should* point to the start of a substitution, parses and
   * returns the substitution, or prints an error message and returns null.
   */
  private Substitution readSubstitution(CommandParsingStatus input, Renaming keyNames) {
    if (_proof.getProofState().isFinalState()) {
      _module.println("The proof state is empty; there is nothing to reduce.");
      return null;
    }
    MutableRenaming valueNames = _proof.getProofState().getTopEquation().getRenamingCopy();
    return input.readSubstitution(_proof.getContext().getTRS(), keyNames, valueNames, _module);
  }
}

