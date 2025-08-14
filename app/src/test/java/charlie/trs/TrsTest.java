/**************************************************************************************************
 Copyright 2024, 2025 Cynthia Kop

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

import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.TreeSet;

import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.*;
import charlie.trs.TrsProperties.*;
import charlie.trs.TRS.RuleScheme;
import charlie.reader.CoraInputReader;

public class TrsTest {
  private Type type(String txt) {
    try { return CoraInputReader.readType(txt); }
    catch (Exception e) { System.out.println(e); return null; }
  }

  private FunctionSymbol makeConstant(String name, String ty) {
    return TermFactory.createConstant(name, type(ty));
  }

  private FunctionSymbol a = makeConstant("A", "a");
  private FunctionSymbol b = makeConstant("B", "b");
  private FunctionSymbol f = makeConstant("f", "a -> b -> a");
  private FunctionSymbol g = makeConstant("g", "Int -> a");
  private FunctionSymbol h = makeConstant("h", "(a -> b) -> a -> b");
  private TRS _mstrs = null;
  private TRS _lctrs = null;
  private TRS _strs = null;
  private TRS _lcstrs = null;
  private TRS _cfs = null;
  private TRS _ams = null;
  private TRS _cora = null;

  private void setupTRSs() {
    if (_mstrs != null) return;   // we've called this before
    Alphabet alf = new Alphabet(List.of(f,g,h,a,b));
    List<Rule> empty = List.of();
    _mstrs = TrsFactory.createTrs(new Alphabet(List.of(f,g,a,b)), empty, TrsFactory.MSTRS);
    _lctrs = TrsFactory.createTrs(new Alphabet(List.of(f,g,a,b)), empty, TrsFactory.LCTRS);
    _strs = TrsFactory.createTrs(alf, empty, TrsFactory.STRS);
    _lcstrs = TrsFactory.createTrs(alf, empty, TrsFactory.LCSTRS);
    _cfs = TrsFactory.createTrs(alf, empty, TrsFactory.CFS);
    _ams = TrsFactory.createTrs(alf, empty, TrsFactory.AMS);
    _cora = TrsFactory.createTrs(alf, empty, TrsFactory.CORA);
  }

  @Test
  public void testTermsAllowedLevel() {
    setupTRSs();
    // f(a, B): a first-order term that is allowed everywhere
    Term fab = TermFactory.createApp(f, a, b);
    assertTrue(_mstrs.termAllowed(fab));
    assertTrue(_lctrs.termAllowed(fab));
    assertTrue(_strs.termAllowed(fab));
    // f(a): a higher-order term that is allowed in any of the higher-order TRSs
    Term fa = f.apply(a);
    assertFalse(_mstrs.termAllowed(fa));
    assertFalse(_lctrs.termAllowed(fa));
    assertTrue(_strs.termAllowed(fa));
    assertTrue(_lcstrs.termAllowed(fa));
    assertTrue(_cfs.termAllowed(fa));
    // h(λx.B, A): this is only allowed in those kinds where lambda is permitted
    Variable x = TermFactory.createBinder("x", type("a"));
    Term s = TermFactory.createApp(h, TermFactory.createAbstraction(x, b), a);
    assertFalse(_mstrs.termAllowed(s));
    assertFalse(_lctrs.termAllowed(s));
    assertFalse(_strs.termAllowed(s));
    assertFalse(_lcstrs.termAllowed(s));
    assertTrue(_cfs.termAllowed(s));
    assertTrue(_ams.termAllowed(s));
    assertTrue(_cora.termAllowed(s));
  }

  @Test
  public void testTermsAllowedTheories() {
    setupTRSs();
    // [+](1) and x + 3
    Term one = TheoryFactory.createValue(1);
    Term x = TermFactory.createVar("x", one.queryType());
    Term highertheory = TheoryFactory.plusSymbol.apply(one);
    Term lowertheory = TermFactory.createApp(TheoryFactory.plusSymbol, one, x);

    assertFalse(_mstrs.termAllowed(lowertheory));
    assertTrue(_lctrs.termAllowed(lowertheory));
    assertFalse(_strs.termAllowed(highertheory));
    assertFalse(_lctrs.termAllowed(highertheory));
    assertTrue(_lcstrs.termAllowed(highertheory));
    assertFalse(_cfs.termAllowed(lowertheory));
    assertFalse(_ams.termAllowed(highertheory));
    assertTrue(_cora.termAllowed(highertheory));

    // a variable of boolean type
    Term y = TheoryFactory.createVar("y", TypeFactory.boolSort);
    assertTrue(_mstrs.termAllowed(y));

    // a hidden theory symbol: (λx.a) 1
    Term abs = TermFactory.createAbstraction(TermFactory.createBinder("x", one.queryType()), a);
    Term s = abs.apply(one);
    assertFalse(_lcstrs.termAllowed(s));  // because of the lambda
    assertFalse(_cfs.termAllowed(s));     // because of the theory
    assertFalse(_ams.termAllowed(s));     // because of the theory
    assertTrue(_cora.termAllowed(s));
  }

  @Test
  public void testTermsAllowedTuples() {
    setupTRSs();
    Term x = TermFactory.createVar("x", type("⦇ a , b ⦈"));
    Term z = TermFactory.createVar("y", type("⦇ a , b ⦈ -> c"));
    Term zx = z.apply(x);
    assertFalse(_mstrs.termAllowed(x));
    assertFalse(_lctrs.termAllowed(x));
    assertFalse(_cfs.termAllowed(zx));
    assertFalse(_lcstrs.termAllowed(z));
    assertFalse(_ams.termAllowed(zx));
    assertTrue(_cora.termAllowed(zx));
  }

  @Test
  public void testVerifyPropertiesWithoutRules() {
    setupTRSs();
    assertTrue(_mstrs.verifyProperties(Level.FIRSTORDER, Constrained.NO, TypeLevel.SIMPLE,
                                       Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
    assertFalse(_lctrs.verifyProperties(Level.FIRSTORDER, Constrained.NO, TypeLevel.SIMPLE,
                                        Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
    assertTrue(_lctrs.verifyProperties(Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE,
                                       Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
    assertTrue(_lcstrs.verifyProperties(Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE,
                                        Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
    assertFalse(_cfs.verifyProperties(Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE,
                                      Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
    assertFalse(_cora.verifyProperties(Level.META, Constrained.YES, TypeLevel.SIMPLE,
                                       Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
    assertTrue(_cora.verifyProperties(Level.META, Constrained.YES, TypeLevel.SIMPLEPRODUCTS,
                                      Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
  }

  @Test
  public void testDerivedProperties() {
    Alphabet alf = new Alphabet(List.of(f, a, b));
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    rules.add(TrsFactory.createRule(TermFactory.createApp(f, x, b), x));
    TRS trs = TrsFactory.createTrs(alf, rules, TrsFactory.CORA);
    assertTrue(trs.theoriesIncluded());
    assertTrue(trs.productsIncluded());
    assertFalse(trs.isApplicative());
    assertTrue(trs.verifyProperties(Level.FIRSTORDER, Constrained.NO, TypeLevel.SIMPLE,
                                    Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE, TermLevel.LAMBDA,
                                    Constrained.YES, TypeLevel.SIMPLEPRODUCTS));
    assertFalse(trs.verifyProperties(Level.FIRSTORDER, Constrained.NO, TypeLevel.SIMPLE,
                                     Lhs.PATTERN, Root.FUNCTION, FreshRight.CVARS));
  }

  @Test
  public void testVerifyPropertiesWithRules() {
    Variable z = TermFactory.createVar("Z", type("a -> b"));
    Variable y = TermFactory.createVar("y", type("a"));
    Variable x = TermFactory.createBinder("x", type("a"));
    Variable u = TermFactory.createVar("u", type("Int"));
    
    // h(Z, y) -> h(λx.b, y)
    Rule rule1 = TrsFactory.createRule(TermFactory.createApp(h, z, y),
                   TermFactory.createApp(h, TermFactory.createAbstraction(x, b), y));
    // Z(A) -> B
    Rule rule2 = TrsFactory.createRule(z.apply(a), b);
    // g(u) -> A | u > 0
    Rule rule3 = TrsFactory.createRule(g.apply(u), a, TermFactory.createApp(
      TheoryFactory.greaterSymbol, u, TheoryFactory.createValue(0)));
    // A -> g(u) | u < 0
    Rule rule4 = TrsFactory.createRule(a, g.apply(u), TermFactory.createApp(
      TheoryFactory.smallerSymbol, u, TheoryFactory.createValue(0)));
    // f(A, B) -> y
    Rule rule5 = TrsFactory.createRule(f.apply(a).apply(b), y);

    Alphabet alf = new Alphabet(List.of(f,g,h,a,b));
    TRS ams1 = TrsFactory.createTrs(alf, List.of(rule1), TrsFactory.AMS);
    TRS ams2 = TrsFactory.createTrs(alf, List.of(rule1, rule2), TrsFactory.AMS);
    TRS ams3 = TrsFactory.createTrs(alf, List.of(rule1, rule2), Set.of("f"), true, TrsFactory.AMS);
    TRS lcstrs1 = TrsFactory.createTrs(alf, List.of(rule3), TrsFactory.LCSTRS);
    TRS lcstrs2 = TrsFactory.createTrs(alf, List.of(rule2, rule3, rule4), TrsFactory.LCSTRS);
    TRS cora = TrsFactory.createTrs(alf, List.of(rule5), TrsFactory.CORA);

    assertTrue(ams1.verifyProperties(
      Level.LAMBDA, Constrained.NO, TypeLevel.SIMPLE, Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
    assertFalse(ams2.verifyProperties(
      Level.LAMBDA, Constrained.NO, TypeLevel.SIMPLE, Lhs.PATTERN, Root.FUNCTION, FreshRight.NONE));
    assertTrue(ams2.verifyProperties(
      Level.LAMBDA, Constrained.NO, TypeLevel.SIMPLE, Lhs.SEMIPATTERN, Root.ANY, FreshRight.NONE));
    assertFalse(ams3.verifyProperties(
      Level.LAMBDA, Constrained.NO, TypeLevel.SIMPLE, Lhs.SEMIPATTERN, Root.ANY, FreshRight.NONE));
    assertTrue(ams3.verifyProperties(
      Level.LAMBDA, Constrained.NO, TypeLevel.SIMPLE, Lhs.SEMIPATTERN, Root.ANY, FreshRight.CVARS,
      RuleScheme.Eta));

    assertTrue(lcstrs1.verifyProperties(
      Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE, Lhs.PATTERN, Root.FUNCTION,
      FreshRight.NONE));
    assertFalse(lcstrs1.verifyProperties(
      Level.FIRSTORDER, Constrained.YES, TypeLevel.SIMPLE, Lhs.PATTERN, Root.FUNCTION,
      FreshRight.NONE));
    assertTrue(lcstrs1.verifyProperties(
      Level.FIRSTORDER, Constrained.YES, TypeLevel.SIMPLE, Lhs.PATTERN, Root.FUNCTION,
      FreshRight.NONE, TermLevel.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE));
    
    assertFalse(lcstrs2.verifyProperties(
      Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE, Lhs.PATTERN, Root.FUNCTION,
      FreshRight.ANY));
    assertTrue(lcstrs2.verifyProperties(
      Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE, Lhs.SEMIPATTERN, Root.ANY,
      FreshRight.CVARS));
    assertFalse(lcstrs2.verifyProperties(
      Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE, Lhs.SEMIPATTERN, Root.ANY,
      FreshRight.NONE));

    assertTrue(cora.verifyProperties(Level.FIRSTORDER, Constrained.NO, TypeLevel.SIMPLE,
      Lhs.PATTERN, Root.FUNCTION, FreshRight.ANY, TermLevel.LAMBDA, Constrained.YES,
      TypeLevel.SIMPLEPRODUCTS));
    assertFalse(cora.verifyProperties(Level.FIRSTORDER, Constrained.NO, TypeLevel.SIMPLE,
      Lhs.PATTERN, Root.FUNCTION, FreshRight.CVARS));
  }

  @Test
  public void testNoDefinedSymbols() {
    setupTRSs();
    assertTrue(_lcstrs.definedSymbols().size() == 0);
    assertFalse(_mstrs.isDefined(f));
  }

  @Test
  public void testDefinedSymbols() {
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Term fxb = TermFactory.createApp(f, x, b);
    rules.add(TrsFactory.createRule(fxb, x)); // f(x, B) -> x
    Variable y = TermFactory.createVar("y", type("Int"));
    Term zero = TheoryFactory.createValue(0);
    Term constraint = TermFactory.createApp(TheoryFactory.greaterSymbol, y, zero);
    rules.add(TrsFactory.createRule(g.apply(y), a, constraint)); // g(y) -> 0 | x > 0
    Variable z = TermFactory.createVar("Z", type("a -> b -> a"));
    Term zab = TermFactory.createApp(z, a, b);
    rules.add(TrsFactory.createRule(zab, a)); // Z(A,B) -> A
    Alphabet alf = new Alphabet(List.of(f,g,h,a,b));
    TRS trs = TrsFactory.createTrs(alf, rules, TrsFactory.CORA);
    TreeSet<FunctionSymbol> defineds = trs.definedSymbols();
    assertTrue(defineds.size() == 2);
    assertTrue(defineds.contains(f));
    assertTrue(defineds.contains(g));
    assertFalse(defineds.contains(h));
    defineds.add(h);
    assertTrue(trs.definedSymbols().size() == 2);
  }

  @Test
  public void testSymbolNames() {
    setupTRSs();
    Set<String> names = _ams.queryFunctionSymbolNames();
    assertTrue(names.size() == 5);
    assertTrue(names.contains("A"));
    assertTrue(names.contains("B"));
    assertTrue(names.contains("f"));
    assertTrue(names.contains("g"));
    assertTrue(names.contains("h"));
  }

  @Test
  public void testLeftLinearity() {
    Alphabet alf = new Alphabet(List.of(f,g,h,a,b));
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Term fxb = TermFactory.createApp(f, x, b);
    rules.add(TrsFactory.createRule(fxb, x)); // f(x, B) -> x
    TRS trs = TrsFactory.createTrs(alf, rules, TrsFactory.STRS);
    assertTrue(trs.isLeftLinear());
    Term plus = TermFactory.createApp(TheoryFactory.plusSymbol, y, y);
    Term left = g.apply(plus);
    rules.add(TrsFactory.createRule(left, a));  // g(y+y) -> A
    trs = TrsFactory.createTrs(alf, rules, TrsFactory.LCSTRS);
    assertFalse(trs.isLeftLinear());
  }

  @Test
  public void testQueryRulesForSymbolFact() {
    TRS trs = CoraInputReader.readTrsFromString(
      "fact :: Int -> (Int -> o) -> o\n" +
      "comp :: (Int -> o) -> (Int -> Int) -> Int -> o\n" +
      "fact(n, k) -> k(1) | n <= 0\n" +
      "fact(n, k) -> fact(n - 1, comp(k, [*](n))) | n > 0\n" +
      "comp(g, f, x) -> g(f(x))\n");
    FunctionSymbol fact = makeConstant("fact", "Int -> (Int -> o) -> o");
    List<Rule> factRules = trs.queryRulesForSymbol(fact, false).toList();
    assertEquals(2, factRules.size());
    assertTrue(factRules.stream().allMatch(r -> fact.equals(r.queryRoot())));

    FunctionSymbol comp = makeConstant("comp", "(Int -> o) -> (Int -> Int) -> Int -> o");
    List<Rule> compRules = trs.queryRulesForSymbol(comp, true).toList();
    assertEquals(1, compRules.size());
    assertTrue(compRules.stream().allMatch(r -> comp.equals(r.queryRoot())));

    FunctionSymbol udef = makeConstant("udef", "o");
    assertEquals(0, trs.queryRulesForSymbol(udef, false).count());
  }

  @Test
  public void testQueryRulesForSymbolVarHead() {
    TRS trs = CoraInputReader.readTrsFromString(
      "{ F :: a -> a } F(x) -> x\n" +
      "{ G :: b -> a -> a } G(x, y) -> y\n");
    FunctionSymbol f = makeConstant("f", "a -> a");
    List<Rule> fVarRules = trs.queryRulesForSymbol(f, true).toList();
    assertEquals(1, fVarRules.size());
    assertTrue(fVarRules.stream().allMatch(
      r -> r.queryLeftSide().queryHead().queryType().equals(type("a → a"))));

    FunctionSymbol fg = makeConstant("fg", "c -> b -> a -> a");
    assertEquals(2, trs.queryRulesForSymbol(fg, true).count());
    assertEquals(0, trs.queryRulesForSymbol(fg, false).count());

    FunctionSymbol h = makeConstant("h", "b -> a -> b");
    assertEquals(0, trs.queryRulesForSymbol(h, true).count());

    FunctionSymbol i = makeConstant("i", "a");
    assertEquals(0, trs.queryRulesForSymbol(i, true).count());
  }

  @Test
  public void testRuleArity() {
    TRS trs = CoraInputReader.readTrsFromString(
      "fact :: Int -> (Int -> o) -> o\n" +
      "comp :: (Int -> o) -> (Int -> Int) -> Int -> o\n" +
      "fact(n, k) -> k(1) | n <= 0\n" +
      "fact(n, k) -> fact(n - 1, comp(k, [*](n))) | n > 0\n" +
      "comp(g, f, x) -> g(f(x))\n" +
      "error :: Int\n" +
      "[+](error, y) -> error()\n" +
      "[*](error) -> [+](error)\n" +
      "s :: Nat -> Nat\n" +
      "nul :: Nat\n" +
      "id :: Nat -> Nat\n" +
      "id(n) -> n\n" +
      "add :: Nat -> Nat -> Nat\n" +
      "add(s(x), y) -> add(x, s(y))\n" +
      "add(nul) -> id\n"
    );
    Alphabet alf = trs.queryAlphabet();
    assertTrue(trs.queryRuleArity(alf.lookup("fact")) == 2);
    assertTrue(trs.queryRuleArity(alf.lookup("comp")) == 3);
    assertTrue(trs.queryRuleArity(alf.lookup("error")) == 0);
    assertTrue(trs.queryRuleArity(alf.lookup("s")) == 0);
    assertTrue(trs.queryRuleArity(alf.lookup("id")) == 1);
    assertTrue(trs.queryRuleArity(alf.lookup("add")) == -1);
    assertTrue(trs.queryRuleArity(TheoryFactory.plusSymbol) == 2);
    assertTrue(trs.queryRuleArity(TheoryFactory.minusSymbol) == 1);
    assertTrue(trs.queryRuleArity(TheoryFactory.timesSymbol) == -1);
  }
}

