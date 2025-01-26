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

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;

import charlie.terms.FunctionSymbol;
import charlie.terms.Renaming;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

class ProofContextTest {
  private TRS setupTRS() {
    return CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum1(x) -> 0 | x <= 0\n" +
      "sum1(x) -> x + sum1(x-1) | x > 0\n" +
      "sum2 :: Int -> Int\n" +
      "sum2(x) -> iter(x, 0, 0)\n" +
      "iter :: Int -> Int -> Int -> Int\n" +
      "iter(x, i, z) -> z | i > x\n" +
      "iter(x, i, z) -> iter(x, i+1, z+i) | i <= x\n" +
      "o :: nat\n" +
      "s :: nat -> nat\n" +
      "add :: (| nat , nat |) -> nat\n" +
      "add( (|x, o|) ) -> x\n" +
      "add( (|x, s(y) |) ) -> add( (| s(x),y |) )\n" +
      "something :: Int -> Int -> (| Bool , Int |)\n");
  }

  @Test
  public void testConstructors() {
    TRS trs = setupTRS();
    ProofContext context = new ProofContext(trs, lst -> new Renaming(Set.of()));
    assertTrue(context.getConstructors(CoraInputReader.readType("Int")).isEmpty());
    assertTrue(context.getConstructors(CoraInputReader.readType("Bool")).isEmpty());
    Set<FunctionSymbol> funcs = context.getConstructors(CoraInputReader.readType("nat"));
    assertTrue(funcs.size() == 2);
    assertTrue(funcs.contains(trs.lookupSymbol("o")));
    assertTrue(funcs.contains(trs.lookupSymbol("s")));
    assertFalse(funcs.contains(trs.lookupSymbol("add")));
    funcs = context.getConstructors(CoraInputReader.readType("(|Bool,Int|)"));
    assertTrue(funcs.size() == 1);
  }
}

