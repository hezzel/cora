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

package cora.termination.transformation;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import charlie.terms.*;
import charlie.trs.*;
import charlie.reader.CoraInputReader;
import cora.io.*;
import cora.termination.transformation.HelperFunctionTransformer.Candidate;

public class CallByValueModifierTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt, TrsFactory.LCSTRS);
  }

  @Test
  public void testModify() {
    TRS trs = makeTrs(
      "f :: Int -> Int -> Int\n" +
      "f(x,y) -> f(x+1,y)\n" +
      "f(x,z) -> f(1,2) | x >= z\n" +
      "f(y,z) -> f(1,y) | y >= 0\n"
    );
    assertTrue(CallByValueModifier.isApplicable(trs));
    TRS replacement = CallByValueModifier.modify(trs);
    assertTrue(replacement.queryRuleCount() == 3);
    assertTrue(replacement.queryRule(0).toString().equals("f(x, y) → f(x + 1, y) | x = x ∧ y = y"));
    assertTrue(replacement.queryRule(1).toString().equals("f(x, z) → f(1, 2) | x ≥ z"));
    assertTrue(replacement.queryRule(2).toString().equals("f(y, z) → f(1, y) | y ≥ 0 ∧ z = z"));
  }

  @Test
  public void testNotApplicable() {
    TRS trs = makeTrs(
      "f :: Int -> Int -> Int\n" +
      "c :: Nat -> Int\n" +
      "f(x,y) -> f(x+1,y)\n" +
      "f(x,z) -> f(1,2) | x >= z\n" +
      "f(y,z) -> f(1,y) | y >= 0\n"
    );
    assertFalse(CallByValueModifier.isApplicable(trs));
  }
}

