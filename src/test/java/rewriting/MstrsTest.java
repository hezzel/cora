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

public class MstrsTest {
  private Type baseType(String name) {
    return TypeFactory.createSort(name);
  }

  private Type arrowType(String name1, String name2) {
    return TypeFactory.createArrow(baseType(name1), baseType(name2));
  }

  private FunctionSymbol a() {
    return TermFactory.createConstant("a", 0);
  }

  private FunctionSymbol b() {
    return TermFactory.createConstant("b", 0);
  }

  private FunctionSymbol f() {
    return TermFactory.createConstant("f", 2);
  }

  private FunctionSymbol g() {
    return TermFactory.createConstant("g", 3);
  }

  private MSTRS createTermRewritingSystem() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());
    symbols.add(b());
    symbols.add(f());
    symbols.add(g());
    Alphabet alf = new Alphabet(symbols);

    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x");
    Term left1 = TermFactory.createApp(f(), x, a());
    Term right1 = x;
    rules.add(new FirstOrderRule(left1, right1));
      // f(x, a) -> x

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(x);
    args.add(x);
    args.add(b());
    Term left2 = TermFactory.createApp(g(), args);
    Term right2 = TermFactory.createApp(f(), b(), x);
    rules.add(new FirstOrderRule(left2, right2));
      // g(x, x, b) -> f(b, x)

    return new MSTRS(alf, rules);
  }

  @Test
  public void testLeftmostInnermostRedex() {
    MSTRS trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), g(b, b, b)), b)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    Position pos = trs.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("2.2.ε"));
  }

  @Test
  public void testLeftmostInnermostReduction() {
    MSTRS trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), g(b, b, b)), b)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    String reduct = trs.leftmostInnermostReduce(term).toString();
    assertTrue(reduct.equals("g(f(a, b), f(g(a, b, a), f(b, b)), b)"));
  }

  @Test
  public void testLeftmostInnermostIrreducible() {
    MSTRS trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), x), b)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    assertTrue(trs.leftmostInnermostReduce(term) == null);
  }

  @Test(expected = cora.exceptions.IllegalSymbolError.class)
  public void testCreateMSTRSWithIllegalSymbol() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());
    symbols.add(b());
    symbols.add(TermFactory.createConstant("i",
                  TypeFactory.createArrow(arrowType("a", "b"), baseType("a"))));
    symbols.add(f());
    Alphabet alf = new Alphabet(symbols);
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x");
    rules.add(new FirstOrderRule(TermFactory.createApp(f(), x, a()), x));

    new MSTRS(alf, rules);
  }

  @Test(expected = cora.exceptions.IllegalRuleError.class)
  public void testCreateMSTRSWithIllegalRule() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(f());
    FunctionSymbol g = TermFactory.createConstant("g", 2);
    symbols.add(g);
    Alphabet alf = new Alphabet(symbols);
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x");
    rules.add(new AtrsRule(f().apply(x), g.apply(x)));

    new MSTRS(alf, rules);
  }

  @Test
  public void testCreateMSTRSWithLegalAtrsRule() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());
    symbols.add(b());
    symbols.add(f());
    symbols.add(g());
    Alphabet alf = new Alphabet(symbols);
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x");
    rules.add(new AtrsRule(TermFactory.createApp(f(), x, a()),
                           TermFactory.createApp(g().apply(b()), x, x)));

    new MSTRS(alf, rules);
  }
}

