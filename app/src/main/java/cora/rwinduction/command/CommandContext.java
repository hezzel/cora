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
import java.util.HashSet;
import java.util.Optional;
import charlie.util.FixedList;
import charlie.util.Pair;
import charlie.terms.position.PositionFormatException;
import charlie.terms.position.Position;
import charlie.terms.Term;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.deduction.DeductionContext;

/** The syntax for the deduction command CONTEXT. */
public class CommandContext extends DeductionCommand {
  @Override
  public String queryName() {
    return "context";
  }

  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of("context", "context <position_1> ... <position_n>", "context safe");
  }
  
  @Override
  public void printHelp(OutputModule module) {
    module.println("Use this deduction rule without any arguments to split an equation " +
      "f s1 ... sn = f t1 ... tn | constr into the n equations si = ti | constr, regardless of " +
      "whether f is a function symbol or variable.");
    module.println("Use the deduction rule with position arguments to split an equation " +
      "C[s1,...,sn] = C[t1,...,tn] | constr into the n equations si = ti | constr, where the " +
      "arguments indicate the positions of the subterms si/ti.");
    module.println("Using this command typically loses completeness of the proof state, although " +
      "completeness is preserved automatically if possible.  If you wish to be sure that " +
      "completeness is preserved, use semiconstructor (perhaps combined with deletion) instead, " +
      "or use the final syntax of the context command: giving the argument \"safe\" chooses a " +
      "maximal semi-constructor context, which will preserve completeness.");
  }
  
  @Override
  protected DeductionContext createStep(CommandParsingStatus input) {
    ArrayList<Position> posses = readPositions(input);
    if (posses == null) return null;
    if (posses.isEmpty()) return DeductionContext.createStep(_proof, optionalModule(), false);
    return DeductionContext.createStep(_proof, optionalModule(), posses);
  }

  private ArrayList<Position> readPositions(CommandParsingStatus input) {
    ArrayList<Position> posses = new ArrayList<Position>();
    String word = input.nextWord();
    if (word != null && word.equals("safe")) {
      if (!input.commandEnded()) {
        _module.println("Unexpected argument at positin %a: expected end of command.",
          input.currentPosition());
        return null;
      }
      return safePositions();
    }
    while (true) {
      if (word == null) return posses;
      try { posses.add(Position.parse(word)); }
      catch (PositionFormatException e) {
        _module.println("Illegal position %a (character %a): %a", word, e.queryProblemPos(),
          e.queryExplanation());
        return null;
      }
      word = input.nextWord();
    }
  }

  private ArrayList<Position> safePositions() {
    EquationContext ec = _proof.getProofState().getTopEquation();
    ArrayList<Position> posses = new ArrayList<Position>();

    DeductionContext.storeDifferences(ec.getLhs(), ec.getRhs(), _proof.getContext(), posses,
                                      new ArrayList<Pair<Term,Term>>());

    if (posses.size() == 0) {
      _module.println("Both sides are the same; please use DELETE instead.");
      return null;
    }
    if (posses.size() == 1 && posses.get(0).isEmpty()) {
      _module.println("No SEMICONSTRUCTOR step can be applied.");
      return null;
    }

    return posses;
  }

  /** Tab suggestions for this command are the positions that both sides share. */
  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    ret.add(endOfCommandSuggestion());
    if (args.equals("")) ret.add(new TabSuggestion("safe", "keyword"));
    else if (args.equals("safe")) return ret;
    HashSet<Position> given = readPositionsInText(args.split(" "));
    Term lhs = _proof.getProofState().getTopEquation().getLhs();
    Term rhs = _proof.getProofState().getTopEquation().getRhs();
    Printer printer = PrinterFactory.createParseablePrinter(_proof.getContext().getTRS());
    for (Position p : lhs.queryPositions(false)) {
      if (p.isEmpty() || given.contains(p)) continue;
      if (samePath(lhs, rhs, p)) {
        printer.add(p);
        ret.add(new TabSuggestion(printer.toString(), "position"));
        printer.clear();
      }
    }
    return ret;
  }

  /**
   * Helper function for suggestNext: parses all the elements of the given array that are positions
   * and sticks them into the returned set.
   */
  private HashSet<Position> readPositionsInText(String[] text) {
    HashSet<Position> ret = new HashSet<Position>();
    for (String word : text) {
      try { ret.add(Position.parse(word)); }
      catch (PositionFormatException e) { }
    }
    return ret;
  }

  /**
   * If the given (non-final) position occurs in both s and t, and all terms on the route to the
   * position have the same head, then true is returned; otherwise false.
   */
  private boolean samePath(Term s, Term t, Position p) {
    if (p.isFinal()) return true;
    if (!s.queryHead().equals(t.queryHead())) return false;
    int k = p.queryHead();
    if (k <= 0 || k > s.numberArguments() || k > t.numberArguments()) return false;
    return samePath(s.queryArgument(k), t.queryArgument(k), p.queryTail());
  }
}

