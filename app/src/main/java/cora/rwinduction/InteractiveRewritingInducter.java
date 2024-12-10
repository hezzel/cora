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

import charlie.util.Either;
import charlie.util.FixedList;
import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.rwinduction.engine.*;
import cora.rwinduction.tui.*;
import cora.rwinduction.command.Command;
import cora.rwinduction.parser.*;

public class InteractiveRewritingInducter {
  private Inputter _input;
  private Outputter _output;
  private CommandParser _parser;
  private ProverContext _context;

  InteractiveRewritingInducter(Inputter input, Outputter output,
                               CommandParser cparse, ProverContext context) {
    _input = input;
    _output = output;
    _parser = cparse;
    _context = context;
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

  private static CommandParser createCommandParser(TRS trs) {
    CommandParser cp = new CommandParser();
    cp.registerSyntax(new SyntaxMetaQuit());
    cp.registerSyntax(new SyntaxMetaSyntax(cp));
    cp.registerSyntax(new SyntaxMetaRules(trs));
    return cp;
  }

  public static ProofObject run(TRS trs, List<String> inputs, OutputModule output) {
    // set up Inputter, outputter and command parser
    //Inputter inputter = new ReplInputter();
    Inputter inputter = new BasicInputter(); // use BasicInputter if ReplInputter doesn't compile
    Outputter outputter = new Outputter(output);
    if (!inputs.isEmpty()) inputter = new CacheInputter(inputs, inputter);
    CommandParser parser = createCommandParser(trs);
    
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
    ProverContext context = new ProverContext(trs, eqs, outputter.queryTermPrinter());

    // set up the inducter that will do all the work, and run it
    InteractiveRewritingInducter inducter =
      new InteractiveRewritingInducter(inputter, outputter, parser, context);
    return inducter.proveEquivalence();
  }

  private ProofObject proveEquivalence() {
    while (!_context.getProofState().isFinalState()) {
      _output.println("Top equation: %a", _context.getProofState().getTopEquation());
      _output.flush();
      String str = _input.readLine();
      Either<String,Command> result = _parser.parse(str);
      if (result instanceof Either.Left<String,Command>(String s)) _output.println(s);
      if (result instanceof Either.Right<String,Command>(Command cmd)) {
        if (cmd.isQuit()) {
          _input.close();
          return new AbortedProofObject();
        }
        else cmd.run(_context, _output);
      }
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

