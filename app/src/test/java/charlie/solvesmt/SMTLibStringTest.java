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

package charlie.solvesmt;

import charlie.smt.*;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

class SMTLibStringTest {
  @Test
  void buildSmtlibString() {
    SmtProblem smtProblem = new SmtProblem();

    IVar iVar = SmtFactory.createIntegerVariable(smtProblem);
    IVar iVar2 = SmtFactory.createIntegerVariable(smtProblem);
    BVar bVar = SmtFactory.createBooleanVariable(smtProblem);

    Constraint c = SmtFactory.createGeq(iVar, iVar2);
    c = SmtFactory.createConjunction(c, bVar);
    smtProblem.require(c);

    SMTLibString sls = new SMTLibString(SMTLibString.Version.V26, SMTLibString.Logic.QFNIA);
    assertTrue(sls.buildSmtlibString(smtProblem).equals(
            ("(set-info :smt-lib-version 2.6)\n" +
      "(set-logic QF_NIA)\n" +
      "(declare-fun b1() Bool)\n" +
      "(declare-fun i1() Int)\n" +
      "(declare-fun i2() Int)\n" +
      "(assert (>= (+ i1 (- i2)) 0))\n" +
      "(assert b1)\n" +
      "(check-sat)\n" +
      "(get-model)\n" +
      "(exit)\n").replace("\n", System.lineSeparator()))
    );
  }
}
