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

package charlie.trs;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;
import java.util.TreeSet;

import charlie.exceptions.IllegalRuleError;
import charlie.exceptions.IllegalSymbolError;
import charlie.exceptions.NullInitialisationError;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.parser.CoraParser;
import charlie.terms.*;

public class TrsFactoryTrsCreationTest {
  private Type type(String text) {
    return CoraParser.readType(text);
  }

  @Test
  public void testCreateMSTRS() {
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    FunctionSymbol g = TermFactory.createConstant("g", 3);
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a);
    symbols.add(b);
    symbols.add(f);
    symbols.add(g);
    Alphabet alf = new Alphabet(symbols);

    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x");
    Term left1 = TermFactory.createApp(f, x, a);
    Term right1 = x;
    rules.add(new Rule(left1, right1));
      // f(x, a) -> x

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(x);
    args.add(x);
    args.add(b);
    Term left2 = TermFactory.createApp(g, args);
    Term right2 = TermFactory.createApp(f, b, x);
    rules.add(new Rule(left2, right2));
      // g(x, x, b) -> f(b, x)

    TRS trs = TrsFactory.createTrs(alf, rules, TrsFactory.MSTRS);
    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).toString().equals("f(x, a) → x"));
    assertTrue(trs.queryRule(1).toString().equals("g(x, x, b) → f(b, x)"));
    assertTrue(trs.querySchemeCount() == 0);
    assertTrue(trs.lookupSymbol("f").equals(f));
    assertTrue(trs.lookupSymbol("ff") == null);
  }

  @Test
  public void testCreateSTRS() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    FunctionSymbol f = TermFactory.createConstant("f", type("(A → A → B) → A → A → B"));
    FunctionSymbol g = TermFactory.createConstant("g", type("A → A → A → B"));
    FunctionSymbol a = TermFactory.createConstant("a", type("A"));
    Variable x = TermFactory.createVar("x", type("A"));
    Variable y = TermFactory.createVar("y", type("A → A"));
    Variable z = TermFactory.createVar("z", type("A"));
    symbols.add(f);
    symbols.add(g);
    symbols.add(a);
    symbols.add(TermFactory.createConstant("b", type("A")));
    symbols.add(TermFactory.createConstant("i", type("B → A")));
    symbols.add(TermFactory.createConstant("j", type("A → A → A")));
    rules.add(TrsFactory.createRule(
      TermFactory.createApp(f, g.apply(x), a), TermFactory.createApp(g, a, x),
      TrsFactory.AMS));
      // f(g(x), a) -> g(a, x) with g :: A -> B -> A -> B
    rules.add(TrsFactory.createRule(
      TermFactory.createApp(g, y.apply(x), x).apply(z),
      TermFactory.createApp(g, z, x).apply(y.apply(a))));
      // g(y(x), x, z) -> g(z, x, y(a))
    TRS trs = TrsFactory.createTrs(new Alphabet(symbols), rules, TrsFactory.STRS);

    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).toString().equals("f(g(x), a) → g(a, x)"));
    assertTrue(trs.queryRule(1).toString().equals("g(y(x), x, z) → g(z, x, y(a))"));
    assertTrue(trs.querySchemeCount() == 0);
    assertTrue(trs.lookupSymbol("f").equals(
      TermFactory.createConstant("f", type("(A → A → B) → A → A → B"))));
    assertTrue(trs.lookupSymbol("h") == null);
  }

  @Test
  public void testMstrsWithUnusedIllegalSymbol() {
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a);
    symbols.add(b);
    symbols.add(f);
    symbols.add(TermFactory.createConstant("i", type("(a → b) → a")));

    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x");
    rules.add(TrsFactory.createRule(TermFactory.createApp(f, x, a), x));

    assertThrows(charlie.exceptions.IllegalSymbolError.class,
      () -> TrsFactory.createTrs(new Alphabet(symbols), rules, TrsFactory.MSTRS));

    symbols.set(symbols.size()-1, TermFactory.createConstant("i", type("(a * b) → a")));
    assertThrows(charlie.exceptions.IllegalSymbolError.class,
      () -> TrsFactory.createTrs(new Alphabet(symbols), rules, TrsFactory.CFS));
  }

  @Test
  public void testFailToCreateApplicativeTRS() {
    // fail by including a non-applicative rule
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createBinder("x", type("a"));
    FunctionSymbol bb = TermFactory.createConstant("B", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("(a → a) → b"));
    Term abs = TermFactory.createAbstraction(x, x);
    symbols.add(f);
    rules.add(TrsFactory.createRule(f.apply(abs), bb));
    assertThrows(IllegalRuleError.class, () ->
      TrsFactory.createTrs(new Alphabet(symbols), rules, TrsFactory.STRS));
  }

  @Test
  public void testCreateTRSWithNullAlphabet() {
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    rules.add(TrsFactory.createRule(TermFactory.createApp(f, x, y), y));
    assertThrows(NullInitialisationError.class, () ->
      TrsFactory.createTrs(null, rules, TrsFactory.MSTRS));
  }

  @Test
  public void testCreateTRSWithNullRules() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    symbols.add(f);
    assertThrows(NullInitialisationError.class, () ->
      TrsFactory.createTrs(new Alphabet(symbols), null, TrsFactory.LCSTRS));
  }

  @Test
  public void testCreateTRSWithNullRule() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    symbols.add(f);
    rules.add(TrsFactory.createRule(TermFactory.createApp(f, x, y), y));
    rules.add(null);
    assertThrows(NullInitialisationError.class, () ->
      TrsFactory.createTrs(new Alphabet(symbols), rules, TrsFactory.CFS));
  }

  @Test
  public void testExpandTRSAfterCreationDoesNothing() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    symbols.add(f);
    rules.add(TrsFactory.createRule(TermFactory.createApp(f, x, y), y));
    TRS trs = TrsFactory.createTrs(new Alphabet(symbols), rules, TrsFactory.MSTRS);
    FunctionSymbol q = TermFactory.createConstant("q", type("a"));
    symbols.add(q);
    rules.add(TrsFactory.createRule(f, f));
    rules.set(0, TrsFactory.createRule(q, q));
    assertTrue(trs.queryRuleCount() == 1);
    assertTrue(trs.queryRule(0).toString().equals("f(x, y) → y"));
    assertTrue(trs.lookupSymbol("f") == f);
    assertTrue(trs.lookupSymbol("q") == null);
  }

  @Test
  public void testCreateMSTRSWithLegalApplicativeRule() {
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    FunctionSymbol g = TermFactory.createConstant("g", 3);
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a);
    symbols.add(b);
    symbols.add(f);
    Alphabet alf = new Alphabet(symbols);
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x");
    rules.add(TrsFactory.createRule(TermFactory.createApp(f, x, a),
                                    TermFactory.createApp(g.apply(b), x, x),
                                    TrsFactory.LCSTRS));
    TrsFactory.createTrs(alf, rules, TrsFactory.MSTRS);
  }

  private TRS createSemiCFS(boolean includeEta) {
    // f(Z(a), λx.Y) → Z(Y)
    // g(a, X, Y) → g(b, Y, h(λz.z, X))
    // h(Z, X) → Z(X)
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    FunctionSymbol a = TermFactory.createConstant("a", type("A"));
    FunctionSymbol b = TermFactory.createConstant("b", type("A"));
    FunctionSymbol c = TermFactory.createConstant("c", type("B"));
    FunctionSymbol f = TermFactory.createConstant("f", type("B → (B → A) → B"));
    FunctionSymbol g = TermFactory.createConstant("g", type("A → A → A → B"));
    FunctionSymbol h = TermFactory.createConstant("h", type("(A → A) → A → A"));
    Variable x1 = TermFactory.createBinder("x", type("B"));
    Variable y1 = TermFactory.createVar("Y", type("A"));
    Variable z1 = TermFactory.createVar("Z", type("A → B"));
    Variable x2 = TermFactory.createVar("X", type("A"));
    Variable y2 = TermFactory.createVar("Y", type("A"));
    Variable z2 = TermFactory.createBinder("z", type("A"));
    Variable x3 = TermFactory.createVar("X", type("A"));
    Variable z3 = TermFactory.createVar("Z", type("A → A"));
    symbols.add(a);
    symbols.add(b);
    symbols.add(c);
    symbols.add(f);
    symbols.add(g);
    symbols.add(h);
    rules.add(TrsFactory.createRule(
      TermFactory.createApp(f, z1.apply(a), TermFactory.createAbstraction(x1, y1)), z1.apply(y1)));
    Term abs = TermFactory.createAbstraction(z2, z2);
    rules.add(TrsFactory.createRule(
      TermFactory.createApp(g.apply(a), x2, y2),
      TermFactory.createApp(g.apply(b), y2, TermFactory.createApp(h, abs, x2))));
    rules.add(TrsFactory.createRule(TermFactory.createApp(h, z3, x3), z3.apply(x3)));
    return TrsFactory.createTrs(new Alphabet(symbols), rules, new TreeSet<String>(), includeEta,
                                TrsFactory.AMS);
  }

  @Test
  public void testCreateCFSWithoutEta() {
    TRS trs = createSemiCFS(false);
    assertTrue(trs.queryRuleCount() == 3);
    assertTrue(trs.queryRule(0).toString().equals("f(Z(a), λx.Y) → Z(Y)"));
    assertTrue(trs.queryRule(1).toString().equals("g(a, X, Y) → g(b, Y, h(λz.z, X))"));
    assertTrue(trs.queryRule(2).toString().equals("h(Z, X) → Z(X)"));
    assertTrue(trs.querySchemeCount() == 1);
    assertTrue(trs.queryScheme(0) == TRS.RuleScheme.Beta);
    assertTrue(trs.lookupSymbol("f").equals(
      TermFactory.createConstant("f", type("B → (B → A) → B"))));
    assertTrue(trs.lookupSymbol("i") == null);
  }

  @Test
  public void testCreateCFSWithEta() {
    TRS trs = createSemiCFS(true);
    assertTrue(trs.queryRuleCount() == 3);
    assertTrue(trs.queryRule(1).toString().equals("g(a, X, Y) → g(b, Y, h(λz.z, X))"));
    assertTrue(trs.querySchemeCount() == 2);
    assertTrue(trs.queryScheme(0) == TRS.RuleScheme.Beta);
    assertTrue(trs.queryScheme(1) == TRS.RuleScheme.Eta);
    assertTrue(trs.lookupSymbol("h").equals(
      TermFactory.createConstant("h", type("(A → A) → (A → A)"))));
    assertTrue(trs.lookupSymbol("i") == null);
  }
}

