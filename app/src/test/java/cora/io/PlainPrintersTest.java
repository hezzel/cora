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

package cora.io;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;
import charlie.types.Type;
import charlie.terms.Term;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

public class PlainPrintersTest {
  private TRS exampleTrs() {
    return CoraInputReader.readTrsFromString("f :: Int -> Int -> Int\na::Int -> Int\n" +
                                             "g :: ((Int -> Int) -> Int) -> (Int × Bool) -> A");
  }

  @Test
  public void testPrintType() {
    PlainTypePrinter p = new PlainTypePrinter();
    Type type = CoraInputReader.readType("a → (Int -> Bool) → bb");
    assertTrue(p.print(type).equals("a -> (Int -> Bool) -> bb"));
  }

  @Test
  public void testPrintComplexTerm() {
    TRS trs = exampleTrs();
    PlainTermPrinter p = new PlainTermPrinter(new PlainTypePrinter(), Set.of("z"));
    Term term = CoraInputReader.readTerm("g(λx::Int→Int.f(Z⟨x⟩,y), ⦇1,true∧z⦈)", trs);
    assertTrue(p.print(term).equals("g(\\x.f(Z[x], y), (|1, true /\\ z__1|))"));
  }

  @Test
  public void testPrintConstraint() {
    TRS trs = exampleTrs();
    PlainTermPrinter p = new PlainTermPrinter(new PlainTypePrinter(), Set.of("z"));
    Term term = CoraInputReader.readTerm(
      "x % (9 - z) > y / 2 ∧ -x < y ∧ ¬(x ≥ y) ∧ (x ≤ y ∨ 1 / a(x) != 2)", trs);
    assertTrue(p.print(term).equals(
      "x % (9 - z__1) > y / 2 /\\ -x < y /\\ not (x >= y) /\\ (x <= y \\/ 1 / a(x) != 2)"));
  }
}

