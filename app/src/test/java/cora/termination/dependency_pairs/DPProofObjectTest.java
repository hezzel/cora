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
import java.util.List;
import java.util.Optional;
import static org.junit.jupiter.api.Assertions.*;

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

  @Test
  void testFullRun() {
    TRS trs = exampleTrs();
    ProofObject accessibility = makeAccessibilityProof(ProofObject.Answer.YES);
    Problem p1 = DPGenerator.generateProblemFromTrs(trs);
    Problem p2 = new Problem(List.of(p1.getDPList().get(0)), trs);
    Problem p3 = new Problem(List.of(p1.getDPList().get(2)), trs);
    DPProofObject ob = new DPProofObject(accessibility, p1);
    ob.addProcessorProof(new HelperA(p1, List.of(p2, p3)));
    ob.addProcessorProof(new HelperB(p2));

    assertTrue(ob.queryAnswer().equals(ProofObject.Answer.MAYBE));
    String start = 
      "This is totally accessible.\n\n" +
      "We start by computing the following initial DP problem:\n\n" +
      "  P1. (1) ack#(m, 0) ➡ ack#(m - 1, 1) | m > 0\n" +
      "      (2) ack#(m, n) ➡ ack#(m, n - 1) | m > 0 ∧ n > 0\n" +
      "      (3) ack#(m, n) ➡ ack#(m - 1, ack(m, n - 1)) | m > 0 ∧ n > 0\n\n" +
      "***** We apply the helper 1 Processor on P1.\n\n" +
      "This is the first helper.\n\n" +
      "  P2. (1) ack#(m, 0) ➡ ack#(m - 1, 1) | m > 0\n\n" +
      "  P3. (1) ack#(m, n) ➡ ack#(m - 1, ack(m, n - 1)) | m > 0 ∧ n > 0\n\n" +
      "***** We apply the helper 2 Processor on P2.\n\n" +
      "Here's a DP for you: ack#(m, 0) ➡ ack#(m - 1, 1) | m > 0.\n\n";
    OutputModule module = DefaultOutputModule.createUnicodeModule(exampleTrs());
    ob.justify(module);
    assertTrue(module.toString().equals(start));

    ob.setTerminating();
    ob.addProcessorProof(new HelperB(p3));
    assertTrue(ob.queryAnswer().equals(ProofObject.Answer.YES));
    module = DefaultOutputModule.createUnicodeModule(exampleTrs());
    ob.justify(module);
    start +=
      "***** We apply the helper 2 Processor on P3.\n\n" +
      "Here's a DP for you: ack#(m, n) ➡ ack#(m - 1, ack(m, n - 1)) | m > 0 ∧ n > 0.\n\n";
    assertTrue(module.toString().equals(start));

    ob.setFailedProof(p3);
    assertTrue(ob.queryAnswer().equals(ProofObject.Answer.MAYBE));
    module = DefaultOutputModule.createUnicodeModule(exampleTrs());
    ob.justify(module);
    assertTrue(module.toString().equals(start +
      "***** No progress could be made on DP problem P3.\n\n"));
  }
}
