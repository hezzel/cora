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

package cora.termination.dependency_pairs.processors.graph;

import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class GraphProcessorTest {

  @Test
  void processTest() {
    /*
    // We deliberately outcommented the use of TrsFactory.MSTRS here, to use the default CORA
    // format instead (which is not supported by the Approximator, so ends up with a default
    // approximation of "compare root symbols"), so we can avoid using the SMT-solver in a unit
    // test.
    TRS trs = CoraInputReader.readTrsFromString(
      " a :: sort \n b :: sort \n c :: sort \n d :: sort \n" +
      " a -> a \n a -> b \n b -> c \n c -> b", TrsFactory.MSTRS);
    */
    TRS trs = CoraInputReader.readTrsFromString(
      " a :: sort \n b :: sort \n c :: sort \n d :: sort \n" +
      " a -> a \n a -> b \n b -> c \n c -> b");
    GraphProcessor proc = new GraphProcessor();

    Problem dpp = (new DPGenerator(trs)).queryProblem(true, false);
    assertTrue(proc.isApplicable(dpp));
    ProcessorProofObject ob = proc.processDPP(dpp);
    assertTrue(ob.queryInput() == dpp);
    assertTrue(ob.queryResults().size() == 2);
    assertTrue(ob.queryResults().get(0).getDPList().size() +
               ob.queryResults().get(1).getDPList().size() == 3);
    OutputModule module = OutputModule.createUnicodeModule(trs);
    ob.justify(module);
    assertTrue(module.toString().equals(
      "We compute a graph approximation with the following edges:\n\n" +
      "  1: 1 2 \n" +
      "  2: 3 \n" +
      "  3: 4 \n" +
      "  4: 3 \n\n" +
      "There are 2 SCCs.\n\n"));
  }
}
