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

package cora.termination.dependency_pairs.processors.graph;

import charlie.reader.CoraInputReader;
import charlie.trs.TRS;
import cora.config.Settings;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class ReachabilityProcessorTest {

  @Test
  void processDPP() {
    Settings.smtSolver = null;
    TRS trs = CoraInputReader.readTrsFromString(
      "public zero :: nat\n" +
      "public s :: nat -> nat\n" +
      "public start :: nat -> nat -> nat\n" +
      "private add :: nat -> nat -> nat\n" +
      "private mul :: nat -> nat -> nat\n" +
      "start(x,y) -> add(x, y)\n" +
      "add(zero, y) -> y\n" +
      "add(s(x), y) -> s(add(x, y))\n" +
      "mul(zero, y) -> zero\n" +
      "mul(s(x), y) -> add(y, mul(x, y))\n");
    Problem p = (new DPGenerator(trs)).queryProblem(false, false);
    ReachabilityProcessor r = new ReachabilityProcessor();
    ProcessorProofObject ob = r.processDPP(p);
    assertTrue(ob.queryResults().size() == 1);
    assertTrue(ob.queryOutput().getDPList().get(0) == p.getDPList().get(0));
    assertTrue(ob.queryOutput().getDPList().get(1) == p.getDPList().get(1));
    assertFalse(ob.queryOutput().isPrivate(0));
    assertTrue(ob.queryOutput().isPrivate(1));
  }
}
