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

package cora.termination.reduction_pairs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;
import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.terms.FunctionSymbol;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.termination.TerminationAnswer;

public class HorpoResultTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt);
  }

/*
  @Test
  public void testPrecedenceAndStatus() {
    TRS trs = makeTrs("f :: Int -> Int g :: Int -> Int f(x) -> f(x-1) | x > 0 g(x) -> f(x)");
    OrderingProblem problem = OrderingProblem.createStrictProblem(trs);
    TreeMap<String,Integer> prec = new TreeMap<String,Integer>();
    TreeMap<String,Integer> stat = new TreeMap<String,Integer>();
    prec.put("f", 1);
    prec.put("g", 2);
    prec.put("[-]", -1);
    prec.put("[+]", -1);
    stat.put("f", 0);
    stat.put("g", 1);
    stat.put("[+]", 2);
    HorpoResult result = new HorpoResult(problem, Set.of(0, 1), prec, stat, 13);

    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    FunctionSymbol minus = TheoryFactory.minusSymbol;

    assertTrue(result.precedence(f, g) < 0);
    assertTrue(result.precedence(g, f) > 0);
    assertTrue(result.precedence(g, plus) > 0);
    assertTrue(result.precedence(plus, minus) == 0);

    assertTrue(result.status(f).equals("Lex"));
    assertTrue(result.status(g).equals("Lex"));
    assertTrue(result.status(minus).equals("Lex"));
    assertTrue(result.status(plus).equals("Mul_2"));
  }
*/
}

