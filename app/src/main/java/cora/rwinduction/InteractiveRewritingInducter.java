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

package cora.rwinduction;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import charlie.util.Either;
import charlie.util.FixedList;
import charlie.types.Type;
import charlie.parser.lib.ParsingException;
import charlie.terms.FunctionSymbol;
import charlie.trs.TRS;
import charlie.trs.TrsProperties.*;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.config.Settings;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.RIParser;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.command.*;
import cora.rwinduction.tui.*;

public class InteractiveRewritingInducter {
  private Inputter _input;
  private OutputModule _output;
  private CmdList _cmdList;
  private PartialProof _proof;

  InteractiveRewritingInducter(Inputter input, OutputModule output,
                               CmdList lst, PartialProof pp) {
    _input = input;
    _output = output;
    _cmdList = lst;
    _proof = pp;
  }

  /**
   * This reads from input until the user either supplies an existing file, or a number of
   * equations, or :quit, or an empty line.
   * - in case a file is read, its name is returned
   * - in case equations are given, the corresponding list is returned
   * - in case :quit or no equations are given, null is returned
   * - in case something invalid is given, we just ask the user again!
   */
  private static Either<String,FixedList<EquationContext>> readEquationsOrFile(Inputter inputter,
                                                                               TRS trs) {
    FixedList<EquationContext> eqs = null;
    try {
      String firstInput = inputter.readLine("Please input one or more equations, or a file: ");
      if (firstInput.equals(":quit") || firstInput.equals("")) return null;
      File f = new File(firstInput);
      if (f.exists() && !f.isDirectory()) {
        return new Either.Left<String,FixedList<EquationContext>>(firstInput);
      }
      else {
        return new Either.Right<String,FixedList<EquationContext>>(
          EquationParser.parseEquationList(firstInput, trs));
      }
    }
    catch (Exception e) {
      System.out.println("Invalid input: " + e.getMessage());
      return readEquationsOrFile(inputter, trs);
    }
  }

  private static CmdList createCmdList(TRS trs) {
    CmdList clst = new CmdList();

    clst.registerEnvironmentCommand(new CommandQuit());
    clst.registerEnvironmentCommand(new CommandSyntax(clst));
    clst.registerEnvironmentCommand(new CommandHelp(clst));
    clst.registerEnvironmentCommand(new CommandRules());
    clst.registerEnvironmentCommand(new CommandEquations());
    clst.registerEnvironmentCommand(new CommandHypotheses());
    clst.registerEnvironmentCommand(new CommandOrdering());
    clst.registerEnvironmentCommand(new CommandSave());
    clst.registerEnvironmentCommand(new CommandCheck());

    clst.registerEnvironmentCommand(new CommandUndo());
    clst.registerEnvironmentCommand(new CommandRedo());

    clst.registerDeductionCommand(new CommandDelete());
    clst.registerDeductionCommand(new CommandSimplify());
    clst.registerDeductionCommand(new CommandCalc());
    clst.registerDeductionCommand(new CommandCase());
    clst.registerDeductionCommand(new CommandSemiconstructor());
    clst.registerDeductionCommand(new CommandApplication());
    clst.registerDeductionCommand(new CommandInduct());
    clst.registerDeductionCommand(new CommandHypothesis());
    clst.registerDeductionCommand(new CommandEqdelete());
    clst.registerDeductionCommand(new CommandHdelete());
    clst.registerDeductionCommand(new CommandAlter());
    clst.registerDeductionCommand(new CommandPostulate());
    clst.registerDeductionCommand(new CommandGeneralise());
    clst.registerDeductionCommand(new CommandSkip());

    return clst;
  }

  public static ProofObject run(TRS trs, List<String> inputs, OutputModule.Style style) {
    CmdList clst = createCmdList(trs);
    // set up Inputter, outputter and command list
    Inputter inputter = new ReplInputter(clst);
    //Inputter inputter = new BasicInputter(); // use BasicInputter if ReplInputter doesn't compile
    OutputModule outputter = new OutputModule(trs, new OutputPage(), style);
    if (!inputs.isEmpty()) inputter = new CacheInputter(inputs, inputter);
    
    // verify that the TRS is legal
    String problem = checkLegalTrs(trs);
    if (problem != null) return new ProofObject() {
      public Answer queryAnswer() { return Answer.MAYBE; }
      public void justify(OutputModule module) { module.println(problem); }
    };

    outputter.printTrs(trs);

    // get initial equations and set up
    Either<String,FixedList<EquationContext>> e = readEquationsOrFile(inputter, trs);
    PartialProof proof = null;
    if (e != null) switch (e) {
      case Either.Left(String s):
        SaveFile savefile = new SaveFile(s, trs, clst, outputter);
        proof = savefile.restore();
        break;
      case Either.Right(FixedList<EquationContext> eqs):
        proof = new PartialProof(trs, eqs, lst -> outputter.generateUniqueNaming(lst));
        clst.storeContext(proof, outputter);
        break;
    }
    if (proof == null) return new ProofObject() {
      public Answer queryAnswer() { return Answer.MAYBE; }
      public void justify(OutputModule module) { module.println("No valid equations gives."); }
    };

    // set up the inducter that will do all the work, and run it
    InteractiveRewritingInducter inducter =
      new InteractiveRewritingInducter(inputter, outputter, clst, proof);
    return inducter.proveEquivalence();
  }

  private boolean runCommands(List<String> commands, PartialProof proof, CmdList clst, OutputModule outputter) {
    for (String txt : commands) {
      CommandParsingStatus status = new CommandParsingStatus(txt);
      while (!status.done()) {
        while (status.skipSeparator());   // read past ; if there is one
        String cmdname = status.nextWord();
        if (cmdname == null) { outputter.println("Illegal input: %a", cmdname); return false; }
        Command cmd = _cmdList.queryCommand(cmdname);
        if (cmd == null) { outputter.println("Unknown command: %a.", cmdname); return false; }
        else if (!cmd.execute(status)) return false;
        if (!status.commandEnded()) {
          int pos = status.currentPosition();
          outputter.println("Unexpected token %a at position %a: expected a semi-colon or the " +
            "end of the line.", status.nextWord(), pos);
          return false;
        }
      }
    }
    return true;
  }

  /**
   * This reads the given file, which firsts lists a number of equation contexts (marked GOAL),
   * followed by a number of commands.  The equation contexts are parsed and returned; the commands
   * are stored into the list commands.  If there are problems reading the file, or any of the
   * equation contexts are not valid, an appropriate error message is printed to the outputter and
   * null returned.
   */
  private static FixedList<EquationContext> readEquationsFromFile(String filename, TRS trs,
                                        OutputModule outputter, ArrayList<String> commands) {
    FixedList.Builder<EquationContext> builder = new FixedList.Builder<EquationContext>();
    boolean readAny = false;
    try {
      Scanner s = new Scanner(new File(filename));
      while (s.hasNextLine()) {
        String line = s.nextLine();
        if (line.length() > 6 && line.substring(0,6).equals("GOAL E")) {
          EquationContext goal = readGoal(line, trs, outputter);
          if (goal == null) return null;
          builder.add(goal);
          readAny = true;
        }
        else commands.add(line);
      }
      s.close();
    }   
    catch (IOException e) {
      outputter.println("Could not read from file: %a.", e.getMessage());
      return null;
    }
    if (!readAny) {
      outputter.println("No goals are given in input file %a.", filename);
      return null;
    }
    return builder.build();
  }

  /**
   * Reads a goal of the form: GOAL E<index>: <equation context>.  If any parsing issues arise, an
   * error message is printed to the outputter and null returned instead.
   */
  private static EquationContext readGoal(String line, TRS trs, OutputModule outputter) {
    int k = line.indexOf(':');
    if (k == -1) {
      outputter.println("Illegal input line (not of the form GOAL E<number>: <rest>): %a", line);
      return null;
    }
    int id = -1; 
    try { id = Integer.parseInt(line.substring(6, k)); }
    catch (NumberFormatException e) {
      outputter.println("Illegal input line (E is not followed by <integer><colon>): %a", line);
      return null;
    }   
    try {
      EquationContext ec = EquationParser.parseEquationContext(line.substring(k+1), id, trs);
      if (ec != null) return ec;
      outputter.println("Invalid equation context: %a", line);
    }   
    catch (ParsingException e) {
      outputter.println("Illegal input line [%a]: %a", line, e.getMessage());
    }   
    return null;
  }

  /**
   * This checks if the TRS satisfies the requirements to use rewriting induction in the
   * first place.  If it does, null is returned.  If not, a string describing the problem is
   * returned instead.
   */
  private static String checkLegalTrs(TRS trs) {
    if (!trs.verifyProperties(Level.META, Constrained.YES, TypeLevel.SIMPLEPRODUCTS,
                              Lhs.SEMIPATTERN, Root.THEORY, FreshRight.ANY)) {
      return "The TRS does not satisfy the requirements to apply rewriting induction: " +
        "a simply-typed LCSTRS with left-hand sides being functional terms.";
    }
    String ret = checkNoIllegalConstructors(trs);
    if (ret == null) ret = checkConsistentArity(trs);
    if (ret == null) ret = checkStrategy();
    if (ret != null) return ret;
    return RIParser.checkTrs(trs);
  }

  /**
   * Helper function for checkLegalTrs: this verifies that all constructors have a non-theory type
   * as output type.
   */
  private static String checkNoIllegalConstructors(TRS trs) {
    for (FunctionSymbol f : trs.queryAlphabet().getSymbols()) {
      if (trs.isDefined(f)) continue;
      Type output = f.queryType().queryOutputType();
      if (!output.isBaseType() || output.isTheoryType()) {
        return "The TRS does not satisfy the requirements of the present implementation: " +
          "all constructors other than values should have a non-theory sort as output type " +
          "(this is not the case for " + f.queryName() + ").";
      }
    }
    return null;
  }

  /**
   * Helper function for checkLegalTrs: this verifies that all defined symbols have a consistent
   * rule arity.
   */
  private static String checkConsistentArity(TRS trs) {
    for (FunctionSymbol f : trs.definedSymbols()) {
      if (trs.queryRuleArity(f) == -1) {
        return "The TRS does not satisfy the requirements to apply rewriting induction: " +
          "the function symbol " + f.queryName() + " does not have a consistent arity.";
      }
    }
    return null;
  }

  /**
   * Helper function for checkLegalTrs: this verifies that the reduction strategy is supported.
   */
  private static String checkStrategy() {
    switch (Settings.queryRewritingStrategy()) {
      case Settings.Strategy.Full: return null;
      case Settings.Strategy.Innermost: return null;
      case Settings.Strategy.CallByValue: return null;
      default:
        return "The reduction strategy is not supported.  Only full, innermost or call-by-value " +
          "reduction is supported in this module.";
    }
  }

  private ProofObject proveEquivalence() {
    while (!_proof.isDone()) {
      printCurrentState();
      CommandParsingStatus status = new CommandParsingStatus(_input.readLine());
      while (!status.done()) {
        while (status.skipSeparator());   // read past ; if there is one
        String cmdname = status.nextWord();
        if (cmdname == null) break;
        Command cmd = _cmdList.queryCommand(cmdname);
        if (cmd == null) {
          _output.println("Unknown command: %a.  Use \":help commands\" to list available " +
          "commands.", cmdname);
          break;
        }
        else if (_proof.isFinal() && !cmd.isEnvironmentCommand()) {
          _output.println("As there are no goals left, only environment commands can be executed.");
          break;
        }
        else if (!cmd.execute(status)) break;
        if (!status.commandEnded()) {
          int pos = status.currentPosition();
          _output.println("Unexpected token %a at position %a: expected a semi-colon or the " +
            "end of the line.", status.nextWord(), pos);
          break;
        }
      }
    }
    return new RewritingInductionProof(_proof);
  }

  /** Helper function for proveEquivalence */
  private void printCurrentState() {
    if (_proof.isFinal()) {
      _output.println("All goals have been successfully removed!");
      _output.println("To complete the proof, you still need to verify that a suitable ordering " +
        "exists.  You can do this using the :check command.  Other useful environment commands " +
        "can use include:");
      _output.startTable();
      _output.println(":undo -- to go back to the previous proof state");
      _output.println(":quit -- to end the proof process without termination check");
      _output.println(":ordering -- to see the current ordering requirements");
      _output.println(":rules -- to see the current rules (these must also be oriented)");
      _output.println(":check verbose -- to run the termination check and see an elaborate " +
        "explanation of the outcome (particularly useful if the result is a failure)");
      _output.endTable();
    }
    else {
      _output.print("%aGoal:%a ", "\033[1;34m", "\033[0m");
      _proof.getProofState().getTopEquation().prettyPrint(_output, true);
      _output.println();
    }
  }
}

