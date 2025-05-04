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

package cora.rwinduction;

import java.util.List;

import charlie.util.FixedList;
import charlie.trs.TRS;
import charlie.trs.TrsProperties.*;
import cora.io.OutputModule;
import cora.io.ProofObject;
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

  private static FixedList<EquationContext> readEquations(Inputter inputter, TRS trs) {
    try {
      String firstInput = inputter.readLine("Please input one or more equations: ");
      if (firstInput.equals(":quit") || firstInput.equals("")) return null;
      return EquationParser.parseEquationList(firstInput, trs);
    }
    catch (Exception e) {
      System.out.println("Invalid input: " + e.getMessage());
      return readEquations(inputter, trs);
    }
  }

  private static CmdList createCmdList(TRS trs) {
    CmdList clst = new CmdList();

    // environment commands
    clst.registerCommand(new CommandQuit());
    clst.registerCommand(new CommandSyntax(clst));
    clst.registerCommand(new CommandHelp(clst));
    clst.registerCommand(new CommandRules());
    clst.registerCommand(new CommandEquations());
    clst.registerCommand(new CommandHypotheses());
    clst.registerCommand(new CommandOrdering());
    clst.registerCommand(new CommandSkip());

    // deduction commands
    clst.registerCommand(new CommandDelete());
    clst.registerCommand(new CommandSimplify());
    clst.registerCommand(new CommandCalc());
    clst.registerCommand(new CommandCase());
    clst.registerCommand(new CommandSemiconstructor());
    clst.registerCommand(new CommandInduct());
    clst.registerCommand(new CommandHypothesis());
    clst.registerCommand(new CommandEqdelete());
    clst.registerCommand(new CommandAlter());
    clst.registerCommand(new CommandPostulate());

    // other commands
    clst.registerCommand(new CommandUndo());
    clst.registerCommand(new CommandRedo());
    
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
    FixedList<EquationContext> eqs = readEquations(inputter, trs);
    if (eqs == null) return new ProofObject() {
      public Answer queryAnswer() { return Answer.MAYBE; }
      public void justify(OutputModule module) { module.println("No valid equations gives."); }
    };
    PartialProof proof = new PartialProof(trs, eqs, lst -> outputter.generateUniqueNaming(lst));
    clst.storeContext(proof, outputter);

    // set up the inducter that will do all the work, and run it
    InteractiveRewritingInducter inducter =
      new InteractiveRewritingInducter(inputter, outputter, clst, proof);
    return inducter.proveEquivalence();
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
        "(a simply-typed LCSTRS with left-hand sides being functional terms).";
    }
    return RIParser.checkTrs(trs);
  }

  private ProofObject proveEquivalence() {
    while (!_proof.isDone()) {
      _output.print("%aGoal:%a ", "\033[1;34m", "\033[0m");
      _proof.getProofState().getTopEquation().prettyPrint(_output, true);
      _output.println();
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
}

