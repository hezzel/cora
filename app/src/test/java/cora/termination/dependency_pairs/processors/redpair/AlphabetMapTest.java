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

package cora.termination.dependency_pairs.processors.redpair;

import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;
import charlie.terms.TheoryFactory;
import charlie.trs.Alphabet;
import charlie.reader.CoraInputReader;

import java.util.ArrayList;
import java.util.TreeMap;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class AlphabetMapTest {
  private Type type(String str) {
    return CoraInputReader.readType(str);
  }

  @Test
  public void testGetTypes() {
    AlphabetMap map = new AlphabetMap();
    FunctionSymbol f = TermFactory.createConstant("f", type("(a -> b) -> a -> b -> c"));
    
    FunctionSymbol f1 = map.getTranslation(f, 1);
    assertTrue(f1.queryName().equals("f1"));
    assertTrue(f1.queryType().subtype(1).isBaseType());
    assertTrue(f1.queryType().subtype(1).toString().equals("[a → b]"));
    assertTrue(f1.queryType().subtype(2).isBaseType());
    assertTrue(f1.queryType().subtype(2).toString().equals("[a → b → c]"));
    assertTrue(map.getTranslation(f, 1) == f1);

    FunctionSymbol f3 = map.getTranslation(f, 3);
    assertTrue(f1 != f3);
    assertTrue(f3.queryType().toString().equals("[a → b] → a → b → c"));
    assertTrue(f3.queryName().equals("f3"));

    FunctionSymbol ff = TermFactory.createConstant("f", type("(a -> a) -> b -> b -> c"));
    FunctionSymbol ff1 = map.getTranslation(ff, 1);
    assertFalse(f1.equals(ff1));
  }

  @Test
  public void testGetCalculation() {
    AlphabetMap map = new AlphabetMap();
    FunctionSymbol plus = TheoryFactory.plusSymbol;

    FunctionSymbol p1 = map.getTranslation(plus, 1);
    assertTrue(p1.queryName().equals("+1"));
    assertTrue(p1.queryType().toString().equals("Int → [Int → Int]"));
    
    FunctionSymbol p2 = map.getTranslation(plus, 2);
    assertTrue(p2.queryName().equals("+2"));
    assertTrue(p2.queryType().equals(plus.queryType()));
  }

  @Test
  public void testAlphabet() {
    AlphabetMap map = new AlphabetMap();
    FunctionSymbol f = TermFactory.createConstant("f", type("(a -> b) -> a -> b -> c"));
    FunctionSymbol f1 = map.getTranslation(f, 1);
    FunctionSymbol f2 = map.getTranslation(f, 3);
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> a"));
    FunctionSymbol g0 = map.getTranslation(g, 0);
    FunctionSymbol ff = TermFactory.createConstant("f", type("(a -> a) -> b -> b -> c"));
    FunctionSymbol ff1 = map.getTranslation(ff, 1);
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    FunctionSymbol plus1 = map.getTranslation(plus, 1);
    FunctionSymbol plus2 = map.getTranslation(plus, 2);

    Alphabet alphabet = map.generateAlphabet();
    assertTrue(alphabet.toString().equals(
      "+1 : Int → [Int → Int]\n" +
      "+2 : Int → Int → Int\n" +
      "f1 : [a → b] → [a → b → c]\n" +
      "f3 : [a → b] → a → b → c\n" +
      "f_1 : [a → a] → [b → b → c]\n" +
      "g0 : [Int → a]\n"));
  }

  @Test
  public void testGetAll() {
    AlphabetMap map = new AlphabetMap();
    FunctionSymbol f = TermFactory.createConstant("f", type("(a -> b) -> a -> b -> c"));
    FunctionSymbol f1 = map.getTranslation(f, 1);
    FunctionSymbol f2 = map.getTranslation(f, 3);
    FunctionSymbol g = TermFactory.createConstant("g", type("Int -> a"));
    FunctionSymbol g0 = map.getTranslation(g, 0);
    FunctionSymbol ff = TermFactory.createConstant("f", type("(a -> a) -> b -> b -> c"));
    FunctionSymbol ff1 = map.getTranslation(ff, 1);
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    FunctionSymbol plus1 = map.getTranslation(plus, 1);
    FunctionSymbol plus2 = map.getTranslation(plus, 2);

    ArrayList<Pair<Pair<FunctionSymbol,Integer>,FunctionSymbol>> all = map.getAll();
    assertTrue(all.size() == 6);
    assertTrue(all.get(0).fst().fst() == plus);
    assertTrue(all.get(0).fst().snd() == 1);
    assertTrue(all.get(0).snd() == plus1);
    assertTrue(all.get(1).fst().fst() == plus);
    assertTrue(all.get(1).fst().snd() == 2);
    assertTrue(all.get(1).snd() == plus2);
    assertTrue(all.get(2).fst().fst() == ff);
    assertTrue(all.get(2).fst().snd() == 1);
    assertTrue(all.get(2).snd() == ff1);
    assertTrue(all.get(5).fst().fst() == g);
    assertTrue(all.get(5).fst().snd() == 0);
    assertTrue(all.get(5).snd() == g0);
  }
}

