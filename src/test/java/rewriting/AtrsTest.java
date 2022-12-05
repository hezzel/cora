/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rewriting;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.types.*;
import cora.terms.*;
import cora.parsers.CoraInputReader;

public class AtrsTest {
  private Type baseType(String name) {
    return TypeFactory.createSort(name);
  }

  private Type arrowType(String name1, String name2) {
    return TypeFactory.createArrow(baseType(name1), baseType(name2));
  }

  private Type arrowType(Type type1, Type type2) {
    return TypeFactory.createArrow(type1, type2);
  }

  private FunctionSymbol a() {
    return TermFactory.createConstant("a", baseType("A"));
  }

  private FunctionSymbol b() {
    return TermFactory.createConstant("b", baseType("B"));
  }

  private FunctionSymbol f() {
    return TermFactory.createConstant("f", arrowType(baseType("A"), arrowType("B", "B")));
  }

  private FunctionSymbol g() {
    return TermFactory.createConstant("g", arrowType(baseType("B"), arrowType(baseType("A"),
      arrowType("B", "B"))));
  }

  private FunctionSymbol h() {
    return TermFactory.createConstant("h", arrowType("B", "A"));
  }

  private ATRS createTermRewritingSystem() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());   // a : A
    symbols.add(b());   // b : B
    symbols.add(f());   // f : A -> B -> B
    symbols.add(g());   // g : B -> A -> B -> B
    symbols.add(h());   // h : B -> A
    Alphabet alf = new Alphabet(symbols);

    ArrayList<Rule> rules = new ArrayList<Rule>();

    Variable x = TermFactory.createVar("x", baseType("B"));
    rules.add(new AtrsRule(TermFactory.createApp(f(), a(), x), x));
      // f(a, x) -> x : B

    rules.add(new AtrsRule(TermFactory.createApp(g(), x, a()), TermFactory.createApp(f(), a())));
      // g(x, a()) -> f(a) : B -> B

    return new ATRS(alf, rules);
  }

  @Test
  public void testLeftmostInnermostRedex() {
    ATRS trs = createTermRewritingSystem();
    String str = "g(f(x, b), h(g(b, a, b)), g(f(a, b), a, y))";
    Term term = CoraInputReader.readTermFromString(str, trs);
    Position pos = trs.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("2.1.ε"));
  }

  @Test
  public void testLeftmostInnermostReduction() {
    ATRS trs = createTermRewritingSystem();
    String str = "g(f(x, b), h(g(b, a, b)), g(f(a, b), a, y))";
    Term term = CoraInputReader.readTermFromString(str, trs);
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("g(f(x, b), h(f(a, b)), g(f(a, b), a, y))"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("g(f(x, b), h(b), g(f(a, b), a, y))"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("g(f(x, b), h(b), g(b, a, y))"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("g(f(x, b), h(b), f(a, y))"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("g(f(x, b), h(b), y)"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term == null);
  }
}

