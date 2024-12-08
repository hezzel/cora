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
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.rwinduction.engine.*;
import cora.rwinduction.tui.*;
import cora.rwinduction.parser.CommandParser;

public class InteractiveRewritingInducter {
  private Inputter _input;
  private OutputModule _output;
  private ProverContext _context;

  InteractiveRewritingInducter(Inputter input, OutputModule output, ProverContext context) {
    _input = input;
    _output = output;
    _context = context;
  }

  public static ProofObject run(TRS trs, List<String> inputs, OutputModule output) {
    // set up Inputter
    Inputter inputter = new ReplInputter(); // use BasicInputter if ReplInputter doesn't compile
    if (!inputs.isEmpty()) inputter = new CacheInputter(inputs, inputter);
    
    // verify that the TRS is legal
    String problem = CommandParser.checkTrs(trs);
    if (problem != null) return new ProofObject() {
      public Answer queryAnswer() { return Answer.MAYBE; }
      public void justify(OutputModule module) { module.println(problem); }
    };

    output.printTrs(trs);
    output.printToStdout();
    output.clear();

    // get initial equations and set up
    String firstInput = inputter.readLine("Please input one or more equations: ");
    FixedList<Equation> eqs = CommandParser.parseEquationList(firstInput, trs);
    ProverContext context = new ProverContext(trs, eqs, output.queryTermPrinter());

    // set up the inducter that will do all the work, and run it
    InteractiveRewritingInducter inducter =
      new InteractiveRewritingInducter(inputter, output, context);
    return inducter.proveEquivalence();
  }

  private void printEquation(Equation eq) {
    if (eq.isConstrained()) {
      _output.println("%a %{approx} %a | %a", eq.getLhs(), eq.getRhs(), eq.getConstraint());
    }
    else {
      _output.println("%a %{approx} %a", eq.getLhs(), eq.getRhs());
    }
    _output.printToStdout();
    _output.clear();
  }

  private ProofObject proveEquivalence() {
    while (!_context.getProofState().isFinalState()) {
      printEquation(_context.getProofState().getTopEquation());
      String str = _input.readLine();
      if (str.equals(":quit")) {
        _input.close();
        return new AbortedProofObject();
      }
      _output.println("I read: %a", str);
      _output.printToStdout();
      _output.clear();
    }
    return new SuccesfulProofObject(_context);
  }
}

class AbortedProofObject implements ProofObject {
  public Answer queryAnswer() { return Answer.MAYBE; }
  public void justify(OutputModule out) { out.println("Proof attempt was aborted by user."); }
}

class SuccesfulProofObject implements ProofObject {
  private ProverContext _context;
  SuccesfulProofObject(ProverContext context) { _context = context; }
  public Answer queryAnswer() { return Answer.YES; }
  public void justify(OutputModule out) {
    out.startTable();
    for (String s : _context.getCommandHistory()) out.println("%a", s);
    out.endTable();
  }
}

