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

import charlie.util.Pair;
import charlie.util.Either;
import charlie.util.FixedList;
import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.rwinduction.engine.Equation;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.ExtendedTermParser;
import cora.rwinduction.command.*;
import cora.rwinduction.tui.*;

public class InteractiveRewritingInducter {
  private Inputter _input;
  private Outputter _output;
  private CmdList _cmdList;
  private PartialProof _proof;

  InteractiveRewritingInducter(Inputter input, Outputter output,
                               CmdList lst, PartialProof pp) {
    _input = input;
    _output = output;
    _cmdList = lst;
    _proof = pp;
  }

  private static FixedList<Equation> readEquations(Inputter inputter, TRS trs) {
    try {
      String firstInput = inputter.readLine("Please input one or more equations: ");
      if (firstInput.equals(":quit") || firstInput.equals("")) return null;
      return ExtendedTermParser.parseEquationList(firstInput, trs);
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

    // deduction commands
    clst.registerCommand(new CommandDelete());
    clst.registerCommand(new CommandSimplify());
    
    return clst;
  }

  public static ProofObject run(TRS trs, List<String> inputs, OutputModule output) {
    // set up Inputter, outputter and command list
    //Inputter inputter = new ReplInputter();
    Inputter inputter = new BasicInputter(); // use BasicInputter if ReplInputter doesn't compile
    Outputter outputter = new Outputter(output);
    if (!inputs.isEmpty()) inputter = new CacheInputter(inputs, inputter);
    CmdList clst = createCmdList(trs);
    
    // verify that the TRS is legal
    String problem = ExtendedTermParser.checkTrs(trs);
    if (problem != null) return new ProofObject() {
      public Answer queryAnswer() { return Answer.MAYBE; }
      public void justify(OutputModule module) { module.println(problem); }
    };

    outputter.printTrs(trs);
    outputter.flush();

    // get initial equations and set up
    FixedList<Equation> eqs = readEquations(inputter, trs);
    if (eqs == null) return new AbortedProofObject();
    PartialProof proof = new PartialProof(trs, eqs, outputter.queryTermPrinter());
    clst.storeContext(proof, outputter);

    // set up the inducter that will do all the work, and run it
    InteractiveRewritingInducter inducter =
      new InteractiveRewritingInducter(inputter, outputter, clst, proof);
    return inducter.proveEquivalence();
  }

  private ProofObject proveEquivalence() {
    while (!_proof.isDone()) {
      _output.println("Top equation: %a", _proof.getProofState().getTopEquation());
      _output.flush();
      Either<Pair<Command,String>,String> either = _cmdList.parse(_input.readLine());
      switch (either) {
        case Either.Left(Pair<Command,String> p):
          Command cmd = p.fst();
          String args = p.snd();
          cmd.execute(args);
          break;
        case Either.Right(String cmdname):
          _output.println("Unknown command: %a.  Use \":help commands\" to list available " +
            "commands.", cmdname);
          break;
      }
    }
    if (_proof.getProofState().isFinalState()) return new SuccesfulProofObject(_proof);
    else return new AbortedProofObject();
  }
}

class AbortedProofObject implements ProofObject {
  public Answer queryAnswer() { return Answer.MAYBE; }
  public void justify(OutputModule out) { out.println("Proof attempt was aborted by user."); }
}

class SuccesfulProofObject implements ProofObject {
  private PartialProof _proof;
  SuccesfulProofObject(PartialProof pp) { _proof = pp; }
  public Answer queryAnswer() { return Answer.YES; }
  public void justify(OutputModule out) {
    out.startTable();
    for (String s : _proof.getCommandHistory()) out.println("%a", s);
    out.endTable();
  }
}

