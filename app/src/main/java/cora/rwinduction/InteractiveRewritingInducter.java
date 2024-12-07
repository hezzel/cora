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

import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.rwinduction.engine.*;
import cora.rwinduction.tui.*;
import cora.rwinduction.parser.CommandParser;
import java.util.List;

public class InteractiveRewritingInducter {
  private Inputter _input;
  private OutputModule _output;

  InteractiveRewritingInducter(Inputter input, OutputModule output) {
    _input = input;
    _output = output;
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

    // get initial equations
    String firstInput = inputter.readLine("Please input one or more equations: ");
    List<Equation> eqs = CommandParser.parseEquationList(firstInput, trs);
    for (Equation eq : eqs) {
      System.out.println("Got equation: " + eq);
    }

    // set up the inducter that will do all the work, and run it
    InteractiveRewritingInducter inducter = new InteractiveRewritingInducter(inputter, output);
    inducter.test();

    return null;
  }

  private void test() {
    while (true) {
      String str = _input.readLine("Next line please: ");
      if (str.equals(":quit")) {
        _input.close();
        return;
      }
      _output.println("I read: %a", str);
      _output.printToStdout();
      _output.clear();
    }
  }
}

