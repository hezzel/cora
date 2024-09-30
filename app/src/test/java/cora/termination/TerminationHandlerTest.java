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

package cora.termination;

import charlie.types.TypeFactory;
import charlie.terms.Renaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TheoryFactory;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

import java.util.Set;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class TerminationHandlerTest {
  @Test
  void testLVarTransformationNothingDone() {
    TRS trs = CoraInputReader.readTrsFromString(
      "eval :: Int -> Int -> Int\n" +
      "eval(x, y) -> eval(x - 1, y) | x>y");
    assertTrue(TerminationHandler.includeLVarInConstraint(trs) == trs);
  }

  @Test
  public void testLVarTransformationSomethingDone() {
    TRS trs = CoraInputReader.readTrsFromString(
      "eval :: Int -> Int -> Int\n" +
      "eval(x, y) -> eval(x - 1, y) | x>y\n" +
      "eval(x, x) -> eval(x, y)\n" +
      "eval(x, y) -> eval(x + 1, y) | x>y");
    TRS update = TerminationHandler.includeLVarInConstraint(trs);
    assertTrue(update != trs);
    assertTrue(update.queryRuleCount() == 3);
    assertTrue(update.queryRule(0) == trs.queryRule(0));
    assertTrue(update.queryRule(2) == trs.queryRule(2));
    assertTrue(update.queryRule(1).toString().equals("eval(x, x) → eval(x, y) | y = y"));
  }
}
