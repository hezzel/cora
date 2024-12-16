/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.reduction;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.*;
import charlie.reader.CoraInputReader;
import cora.config.Settings;

public class ReducerTest {
  private Type type(String txt) {
    try { return CoraInputReader.readType(txt); }
    catch (Exception e) { System.out.println(e); return null; }
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

  private TRS createMSTRS() {
    Alphabet alf = new Alphabet(List.of(a(), b(), f(), g()));

    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x");
    Term left1 = TermFactory.createApp(f(), x, a());
    Term right1 = x;
    rules.add(TrsFactory.createRule(left1, right1));
      // f(x, a) -> x

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(x);
    args.add(x);
    args.add(b());
    Term left2 = TermFactory.createApp(g(), args);
    Term right2 = TermFactory.createApp(f(), b(), x);
    rules.add(TrsFactory.createRule(left2, right2));
      // g(x, x, b) -> f(b, x)

    return TrsFactory.createTrs(alf, rules, TrsFactory.MSTRS);
  }

  @Test
  public void testLeftmostInnermostRedexMSTRS() {
    TRS trs = createMSTRS();
    Reducer reducer = new Reducer(trs);
    String str = "g(f(a, b), f(g(a, b, a), g(b, b, b)), b)";
    Term term = CoraInputReader.readTerm(str, trs);
    Position pos = reducer.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("2.2"));
  }

  @Test
  public void testLeftmostInnermostMSTRSReduction() {
    TRS trs = createMSTRS();
    Reducer reducer = new Reducer(trs);
    String str = "g(f(a, b), f(g(a, b, a), g(b, b, b)), b)";
    Term term = CoraInputReader.readTerm(str, trs);
    Settings.setStrategy(Settings.Strategy.Innermost);
    String reduct = reducer.reduce(term).toString();
    assertTrue(reduct.equals("g(f(a, b), f(g(a, b, a), f(b, b)), b)"));
  }

  @Test
  public void testLeftmostInnermostIrreducible() {
    TRS trs = createMSTRS();
    Reducer reducer = new Reducer(trs);
    String str = "g(f(a, b), f(g(a, b, a), x), b)";
    Term term = CoraInputReader.readTerm(str, trs);
    Settings.setStrategy(Settings.Strategy.Innermost);
    assertTrue(reducer.reduce(term) == null);
  }

  private TRS createSTRS() {
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
      TermFactory.createApp(f, g.apply(x), a), TermFactory.createApp(g, a, x)));
      // f(g(x), a) -> g(a, x) with g :: A -> B -> A -> B
    rules.add(TrsFactory.createRule(
      TermFactory.createApp(g, y.apply(x), x).apply(z),
      TermFactory.createApp(g, z, x).apply(y.apply(a))));
      // g(y(x), x, z) -> g(z, x, y(a))
    return TrsFactory.createTrs(new Alphabet(symbols), rules, TrsFactory.STRS);
  }

  @Test
  public void testLeftmostInnermostRedexApplicative() {
    // note that although the rule f(g(x), a) -> g(a, x) is *technically* on the
    // left of the redex g(j(a, b), b, a), we consider only maximally applied
    // subterms, so the innermost redex takes precedence
    TRS trs = createSTRS();
    Reducer reducer = new Reducer(trs);
    String str = "f(g(a), a, i(g(j(a,b), b, a)))";
    Term term = CoraInputReader.readTerm(str, trs);
    Position pos = reducer.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("3.1"));
  }

  @Test
  public void testLeftmostInnermostReductionApplicative() {
    TRS trs = createSTRS();
    Reducer reducer = new Reducer(trs);
    String str = "f(g(a), a, i(g(j(a,b), b, a)))";
    Term term = CoraInputReader.readTerm(str, trs);
    Settings.setStrategy(Settings.Strategy.Innermost);
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(g(a), a, i(g(a, b, j(a, a))))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("g(a, a, i(g(a, b, j(a, a))))"));
    term = reducer.reduce(term);
    assertTrue(term == null);
  }

  private TRS createCFS(boolean includeEta) {
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
                                TrsFactory.CFS);
  }

  @Test
  public void testLeftmostInnermostRedexIsRuleRedex() {
    TRS trs = createCFS(true);
    Reducer reducer = new Reducer(trs);
    String str = "f(g(a, b, a), λz.a)";
    Term term = CoraInputReader.readTerm(str, trs);
    Position pos = reducer.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("1"));
  }

  @Test
  public void testLeftmostInnermostRedexIsBetaRedex() {
    TRS trs = createCFS(false);
    Reducer reducer = new Reducer(trs);
    String str = "f(g(a, (λx::A.x)(b), a), λz.a)";
    Term term = CoraInputReader.readTerm(str, trs);
    Position pos = reducer.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("1.2"));
  }

  @Test
  public void testLeftmostInnermostRedexIsEtaRedex() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    FunctionSymbol a = TermFactory.createConstant("a", type("A"));
    FunctionSymbol g = TermFactory.createConstant("g", type("A → A → A"));
    FunctionSymbol h = TermFactory.createConstant("h", type("(A → A) → A → A"));
    symbols.add(a);
    symbols.add(g);
    symbols.add(h);
    Variable z = TermFactory.createVar("Z", type("A → A"));
    Variable y = TermFactory.createVar("Y", type("A"));
    rules.add(TrsFactory.createRule(TermFactory.createApp(h, z, y), z.apply(y)));
    Alphabet alf = new Alphabet(symbols);
    TreeSet<String> empty = new TreeSet<String>();
    TRS trswith = TrsFactory.createTrs(alf, rules, empty, true, TrsFactory.CFS);
    TRS trswithout = TrsFactory.createTrs(alf, rules, empty, false, TrsFactory.CFS);
    Reducer reducerwith = new Reducer(trswith);
    Reducer reducerwithout = new Reducer(trswithout);
    // rule: h(Z, Y) → Z(Y)

    Variable x = TermFactory.createBinder("x", type("A"));
    Term term = TermFactory.createApp(h,
      TermFactory.createAbstraction(x, TermFactory.createApp(g, a, x)),
      TermFactory.createApp(TermFactory.createAbstraction(x, x), a));
    // term: h(λx.g(a, x), (λx.x)(a))

    Position pos;
    pos = reducerwith.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("1"));
    pos = reducerwithout.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("2"));
  }

  @Test
  public void testLeftmostInnermostCFSReduction() {
    TRS trs = createCFS(true);
    Reducer reducer = new Reducer(trs);
    String str = "f(g(a, (λx::A.x)(b), a), λz.a)";
    Term term = CoraInputReader.readTerm(str, trs);
    Settings.setStrategy(Settings.Strategy.Innermost);
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(g(a, b, a), λz.a)"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(g(b, a, h(λz.z, b)), λz.a)"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(g(b, a, (λz.z)(b)), λz.a)"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(g(b, a, b), λz.a)"));
    term = reducer.reduce(term);
    assertTrue(term == null);
  }

  @Test
  public void testCallByValueReduceFirstOrder() {
    TRS trs = createMSTRS();
    Reducer reducer = new Reducer(trs);
    String str = "f(g(x, y, b), g(a, a, b))";
    Term term = CoraInputReader.readTerm(str, trs);
    Settings.setStrategy(Settings.Strategy.CallByValue);
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(g(x, y, b), f(b, a))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(g(x, y, b), b)"));
    term = reducer.reduce(term);
    assertTrue(term == null);
  }

  @Test
  public void testVariablesAreValues() {
    TRS trs = createMSTRS();
    Reducer reducer = new Reducer(trs);
    String str = "f(g(y, y, b), f(a, a))";
    Term term = CoraInputReader.readTerm(str, trs);
    Settings.setStrategy(Settings.Strategy.CallByValue);
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(f(b, y), f(a, a))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("f(f(b, y), a)"));
    term = reducer.reduce(term);  // it matches, but the subterm is not a value
    assertTrue(term == null);
  }

  @Test
  public void testCallByValueWithLambda() {
    TRS trs = CoraInputReader.readTrsFromString(
        "nil :: list\n" +
        "cons :: Int -> list -> list\n" +
        "map :: (Int -> Int) -> list -> list\n" +
        "map(F, nil) -> nil\n" +
        "map(F, cons(H,T)) -> cons(F(H), map(F, T))\n" +
        "add :: Bool -> Int -> Int\n" +
        "add(x, y) -> y + 1 | x\n" +
        "add(x, y) -> y | not x\n",
      TrsFactory.CORA);
    Reducer reducer = new Reducer(trs);
    Term term = CoraInputReader.readTerm("map(λx.add(true \\/ false, x), cons(3, nil))", trs);
    Settings.setStrategy(Settings.Strategy.CallByValue);
    term = reducer.reduce(term);  // we do reduce inside lambda, so long as we're not above a binder
    assertTrue(term.toString().equals("map(λx.add(true, x), cons(3, nil))"));
    term = reducer.reduce(term);  // we do NOT reduce add(true, x)!
    assertTrue(term.toString().equals("cons((λx.add(true, x))(3), map(λx.add(true, x), nil))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("cons(add(true, 3), map(λx.add(true, x), nil))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("cons(3 + 1, map(λx.add(true, x), nil))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("cons(4, map(λx.add(true, x), nil))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("cons(4, nil)"));
    term = reducer.reduce(term);
    assertTrue(term == null);
  }

  @Test
  public void testCallByValueWithPartialApplication() {
    TRS trs = CoraInputReader.readTrsFromString(
        "nil :: list\n" +
        "cons :: Int -> list -> list\n" +
        "map :: (Int -> Int) -> list -> list\n" +
        "map(F, nil) -> nil\n" +
        "map(F, cons(H,T)) -> cons(F(H), map(F, T))\n" +
        "add :: Bool -> Int -> Int\n" +
        "add(x, y) -> y + 1 | x\n" +
        "add(x, y) -> y | not x\n",
      TrsFactory.CORA);
    Reducer reducer = new Reducer(trs);
    Term term = CoraInputReader.readTerm("map(add(true), cons(3, nil))", trs);
    Settings.setStrategy(Settings.Strategy.CallByValue);
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("cons(add(true, 3), map(add(true), nil))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("cons(3 + 1, map(add(true), nil))"));
  }

  @Test
  public void testCBVWithHigherRules() {
    TRS trs = CoraInputReader.readTrsFromString(
        "f :: Int -> Int -> Int -> Int\n" +
        "f(x, y) -> λz::Int.z + x - y | x > y\n" +
        "test1 :: Int -> Bool\n" +
        "test1(x) -> true\n" +
        "test2 :: (Int -> Int) -> Bool\n" +
        "test2(x) -> test1(x(3))\n" +
        "test3 :: (Int -> Int -> Int) -> Bool\n" +
        "test3(x) -> test1(x(37, 42))\n",
      TrsFactory.CORA);
    Reducer reducer = new Reducer(trs);
    Settings.setStrategy(Settings.Strategy.CallByValue);
    Term term1 = CoraInputReader.readTerm("test1(f(7, 2, 3))", trs);
    Term term2a = CoraInputReader.readTerm("test2(f(2, 7))", trs);
    Term term2b = CoraInputReader.readTerm("test2(f(7, 2))", trs);
    Term term3 = CoraInputReader.readTerm("test3(f(7))", trs);

    Term term = reducer.reduce(term1);
    assertTrue(term.toString().equals("test1((λz.z + 7 - 2)(3))"));
    term = reducer.reduce(term);  // the first step is invisible: replacing +(7, -(2)) by +(7, -2)
    assertTrue(term.toString().equals("test1((λz.z + 7 - 2)(3))"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("test1(3 + 7 - 2)"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("test1(10 - 2)"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("test1(8)"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("true"));

    term = reducer.reduce(term2a);
    assertTrue(term == null);

    term = reducer.reduce(term2b);
    assertTrue(term.toString().equals("test2(λz.z + 7 - 2)"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("test2(λz.z + 7 - 2)"));
    term = reducer.reduce(term);
    assertTrue(term.toString().equals("test1((λz.z + 7 - 2)(3))"));
    
    term = reducer.reduce(term3);
    assertTrue(term.toString().equals("test1(f(7, 37, 42))"));
  }
}

