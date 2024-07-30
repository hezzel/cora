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

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.List;

import charlie.smt.*;
import charlie.util.ProcessCaller;

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
      assertEquals("(set-info :smt-lib-version 2.6)" + System.lineSeparator() +
              "(set-logic QF_NIA)" + System.lineSeparator() +
              "(declare-fun b1() Bool)" + System.lineSeparator() +
              "(declare-fun i1() Int)"  + System.lineSeparator() +
              "(declare-fun i2() Int)"  + System.lineSeparator() +
              "(assert (>= (+ i1 (- i2)) 0))" + System.lineSeparator() +
              "(assert b1)" + System.lineSeparator() +
              "(check-sat)" + System.lineSeparator() +
              "(get-model)" + System.lineSeparator() +
              "(exit)" + System.lineSeparator(), sls.buildSmtlibString(smtProblem));
  }
}
