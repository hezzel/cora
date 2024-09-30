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

package cora.termination.dependency_pairs;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.ProofObject;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

class DPProofObjectTest {
  private ProofObject makeAccessibilityProof(ProofObject.Answer answer) {
    return new ProofObject() {
      public ProofObject.Answer queryAnswer() { return answer; }
      public void justify(OutputModule m) {
        if (answer == ProofObject.Answer.YES) m.println("This is totally accessible.");
        else m.println("This is not accessible!");
      }
    };
  }

  private TRS exampleTrs() {
    return CoraInputReader.readTrsFromString(
      "ack :: Int -> Int -> Int\n" +
      "ack(0, n) -> n + 1\n" +
      "ack(m,0) -> ack(m-1, 1) | m > 0\n" +
      "ack(m,n) -> ack(m-1, ack(m,n-1)) | m > 0 ∧ n > 0\n");
  }

  @Test
  public void testNotAccessible() {
    DPProofObject ob = new DPProofObject(makeAccessibilityProof(ProofObject.Answer.NO));
    assertTrue(ob.queryAnswer() == ProofObject.Answer.MAYBE);
    OutputModule module = DefaultOutputModule.createUnicodeModule(exampleTrs());
    ob.justify(module);
    assertTrue(module.toString().equals("This is not accessible!\n\n"));
    // no effect of additional calls (which shouldn't be done anyway)
    ob.addProcessorProof(null);
    ob.setFailedProof(null);
    module = DefaultOutputModule.createUnicodeModule(exampleTrs());
    ob.justify(module);
    assertTrue(module.toString().equals("This is not accessible!\n\n"));
  }

  private class HelperA extends ProcessorProofObject {
    public HelperA(Problem inp, List<Problem> out) { super(inp, out); }
    public String queryProcessorName() { return "helper 1"; }
    public void justify(OutputModule m) { m.println("This is the first helper."); }
  }

  private class HelperB extends ProcessorProofObject {
    public HelperB(Problem inp) { super(inp, List.of()); }
    public String queryProcessorName() { return "helper 2"; }
    public void justify(OutputModule m) {
      m.println("Here's a DP for you: %a.", _input.getDPList().get(0));
    }
  }

  private class HelperC extends ProcessorProofObject {
    private static Problem helperProblem(Problem inp) {
      ArrayList<Rule> newrules = new ArrayList<Rule>();
      for (int i = 2; i < inp.getRuleList().size(); i++) newrules.add(inp.getRuleList().get(i));
      return new Problem(inp.getDPList(), newrules, null, inp.getOriginalTRS(),
                         false, inp.isInnermost(), inp.queryTerminationStatus());
    }
    public HelperC(Problem inp) {
      super(inp, helperProblem(inp));
    }
    public String queryProcessorName() { return "helper 3"; }
    public void justify(OutputModule m) { m.println("This is the rule-removal helper."); }
  }

  @Test
  void testFullRun() {
    TRS trs = exampleTrs();
    ProofObject accessibility = makeAccessibilityProof(ProofObject.Answer.YES);
    Problem p1 = (new DPGenerator(trs)).queryProblem(false, true);
    Problem p2 = p1.removeDPs(Set.of(1, 2), true);
    Problem p3 = p1.removeDPs(Set.of(0, 1), true);
    DPProofObject ob = new DPProofObject(accessibility, p1);
    ob.addProcessorProof(new HelperA(p1, List.of(p2, p3)));
    ob.addProcessorProof(new HelperB(p2));
    HelperC helper = new HelperC(p3);
    ob.addProcessorProof(helper);
    helper = new HelperC(helper.queryOutput());
    ob.addProcessorProof(helper);
    Problem p4 = helper.queryOutput();

    assertTrue(ob.queryAnswer().equals(ProofObject.Answer.MAYBE));
    String start = 
      "This is totally accessible.\n\n" +
      "We start by computing the initial DP problem D1 = (P1, R ∪ R_?, f, c), where:\n\n" +
      "  P1. (1) ack#(m, 0) ➡ ack#(m - 1, 1) | m > 0\n" +
      "      (2) ack#(m, n) ➡ ack#(m, n - 1) | m > 0 ∧ n > 0\n" +
      "      (3) ack#(m, n) ➡ ack#(m - 1, ack(m, n - 1)) | m > 0 ∧ n > 0\n\n" +
      "***** We apply the helper 1 Processor on D1 = (P1, R ∪ R_?, f, c).\n\n" +
      "This is the first helper.\n\n" +
      "Processor output: { D2 = (P2, R ∪ R_?, f, c) ; D3 = (P3, R ∪ R_?, f, c) }, where:\n\n" +
      "  P2. (1) ack#(m, 0) ➡ ack#(m - 1, 1) | m > 0\n\n" +
      "  P3. (1) ack#(m, n) ➡ ack#(m - 1, ack(m, n - 1)) | m > 0 ∧ n > 0\n\n" +
      "***** We apply the helper 2 Processor on D2 = (P2, R ∪ R_?, f, c).\n\n" +
      "Here's a DP for you: ack#(m, 0) ➡ ack#(m - 1, 1) | m > 0.\n\n" +
      "Processor output: { }.\n\n" +
      "***** We apply the helper 3 Processor on D3 = (P3, R ∪ R_?, f, c).\n\n" +
      "This is the rule-removal helper.\n\n" +
      "Processor output: { D4 = (P3, R2, f, c) }, where:\n\n" +
      "  R2. (1) ack(m, n) → ack(m - 1, ack(m, n - 1)) | m > 0 ∧ n > 0\n\n" +
      "***** We apply the helper 3 Processor on D4 = (P3, R2, f, c).\n\n" +
      "This is the rule-removal helper.\n\n" +
      "Processor output: { D5 = (P3, ø, f, c) }.\n\n";
    OutputModule module = DefaultOutputModule.createUnicodeModule(exampleTrs());
    ob.justify(module);
    assertTrue(module.toString().equals(start));
    ob.setTerminating();
    ob.addProcessorProof(new HelperB(p4));
    assertTrue(ob.queryAnswer().equals(ProofObject.Answer.YES));
    module = DefaultOutputModule.createUnicodeModule(exampleTrs());
    ob.justify(module);
    start +=
      "***** We apply the helper 2 Processor on D5 = (P3, ø, f, c).\n\n" +
      "Here's a DP for you: ack#(m, n) ➡ ack#(m - 1, ack(m, n - 1)) | m > 0 ∧ n > 0.\n\n" +
      "Processor output: { }.\n\n";
    assertTrue(module.toString().equals(start));

    ob.setFailedProof(p3);
    assertTrue(ob.queryAnswer().equals(ProofObject.Answer.MAYBE));
    module = DefaultOutputModule.createUnicodeModule(exampleTrs());
    ob.justify(module);
    assertTrue(module.toString().equals(start +
      "***** No progress could be made on DP problem D3 = (P3, R ∪ R_?, f, c).\n\n"));
  }
}
