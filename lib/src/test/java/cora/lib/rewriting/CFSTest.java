/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.lib.rewriting;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.lib.exceptions.IllegalRuleError;
import cora.lib.exceptions.NullInitialisationError;
import cora.lib.types.*;
import cora.lib.terms.*;
import cora.lib.parsers.CoraInputReader;

public class CFSTest {
  private Type type(String str) {
    try { return CoraInputReader.readTypeFromString(str); }
    catch (Exception e) { System.out.println(e); return null; }
  }

  private TRS createTermRewritingSystem(boolean includeEta) {
    // f(Z(a), λx.Y) → Z(Y)
    // g(a, X, Y) → g(b, Y, h(λz.z, X))
    // h(Z, X) → Z(X)
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    FunctionSymbol a = TermFactory.createConstant("a", type("A"));
    FunctionSymbol b = TermFactory.createConstant("b", type("A"));
    FunctionSymbol c = TermFactory.createConstant("c", type("B"));
    FunctionSymbol f = TermFactory.createConstant("f", type("B => (B => A) => B"));
    FunctionSymbol g = TermFactory.createConstant("g", type("A => A => A => B"));
    FunctionSymbol h = TermFactory.createConstant("h", type("(A => A) => A => A"));
    Variable x1 = TermFactory.createBinder("x", type("B"));
    Variable y1 = TermFactory.createVar("Y", type("A"));
    Variable z1 = TermFactory.createVar("Z", type("A => B"));
    Variable x2 = TermFactory.createVar("X", type("A"));
    Variable y2 = TermFactory.createVar("Y", type("A"));
    Variable z2 = TermFactory.createBinder("z", type("A"));
    Variable x3 = TermFactory.createVar("X", type("A"));
    Variable z3 = TermFactory.createVar("Z", type("A => A"));
    symbols.add(a);
    symbols.add(b);
    symbols.add(c);
    symbols.add(f);
    symbols.add(g);
    symbols.add(h);
    rules.add(RuleFactory.createRule(
      TermFactory.createApp(f, z1.apply(a), TermFactory.createAbstraction(x1, y1)), z1.apply(y1)));
    Term abs = TermFactory.createAbstraction(z2, z2);
    rules.add(RuleFactory.createRule(
      TermFactory.createApp(g.apply(a), x2, y2),
      TermFactory.createApp(g.apply(b), y2, TermFactory.createApp(h, abs, x2))));
    rules.add(RuleFactory.createRule(TermFactory.createApp(h, z3, x3), z3.apply(x3)));
    return TRSFactory.createCFS(new Alphabet(symbols), rules, includeEta);
  }

  @Test
  public void testCreateCFSWithoutEta() {
    TRS trs = createTermRewritingSystem(false);
    assertTrue(trs.queryRuleCount() == 3);
    assertTrue(trs.queryRule(0).toString().equals("f(Z(a), λx.Y) → Z(Y)"));
    assertTrue(trs.queryRule(1).toString().equals("g(a, X, Y) → g(b, Y, h(λz.z, X))"));
    assertTrue(trs.queryRule(2).toString().equals("h(Z, X) → Z(X)"));
    assertTrue(trs.querySchemeCount() == 1);
    assertTrue(trs.queryScheme(0).isBeta());
    assertFalse(trs.queryScheme(0).isEta());
    assertTrue(trs.lookupSymbol("f").equals(
      TermFactory.createConstant("f", type("B => (B => A) => B"))));
    assertTrue(trs.lookupSymbol("i") == null);
  }

  @Test
  public void testCreateCFSWithEta() {
    TRS trs = createTermRewritingSystem(true);
    assertTrue(trs.queryRuleCount() == 3);
    assertTrue(trs.queryRule(1).toString().equals("g(a, X, Y) → g(b, Y, h(λz.z, X))"));
    assertTrue(trs.querySchemeCount() == 2);
    assertTrue(trs.queryScheme(0).isBeta());
    assertFalse(trs.queryScheme(0).isEta());
    assertTrue(trs.queryScheme(1).isEta());
    assertFalse(trs.queryScheme(1).isBeta());
    assertTrue(trs.lookupSymbol("h").equals(
      TermFactory.createConstant("h", type("(A => A) => (A => A)"))));
    assertTrue(trs.lookupSymbol("i") == null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateCFSWithNullAlphabet() {
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a => b => b"));
    rules.add(RuleFactory.createRule(TermFactory.createApp(f, x, y), y));
    TRSFactory.createCFS(null, rules, true);
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateCFSWithNullRules() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    FunctionSymbol f = TermFactory.createConstant("f", type("a => b => b"));
    symbols.add(f);
    TRSFactory.createCFS(new Alphabet(symbols), null, false);
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateCFSWithNullRule() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a => b => b"));
    symbols.add(f);
    rules.add(RuleFactory.createRule(TermFactory.createApp(f, x, y), y));
    rules.add(null);
    TRSFactory.createCFS(new Alphabet(symbols), rules, true);
  }

  @Test
  public void testExpandCFSAfterCreationDoesNothing() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a => b => b"));
    symbols.add(f);
    rules.add(RuleFactory.createRule(TermFactory.createApp(f, x, y), y));
    TRS trs = TRSFactory.createCFS(new Alphabet(symbols), rules, false);
    FunctionSymbol q = TermFactory.createConstant("q", type("a"));
    symbols.add(q);
    rules.add(RuleFactory.createRule(f, f));
    rules.set(0, RuleFactory.createRule(q, q));
    assertTrue(trs.queryRuleCount() == 1);
    assertTrue(trs.queryRule(0).toString().equals("f(x, y) → y"));
    assertTrue(trs.lookupSymbol("f") == f);
    assertTrue(trs.lookupSymbol("q") == null);
  }

  @Test
  public void testLeftmostInnermostRedexIsRuleRedex() {
    TRS trs = createTermRewritingSystem(true);
    String str = "f(g(a, b, a), λz.a)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    Position pos = trs.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("1.ε"));
  }

  @Test
  public void testLeftmostInnermostRedexIsBetaRedex() {
    TRS trs = createTermRewritingSystem(false);
    String str = "f(g(a, (λx::A.x)(b), a), λz.a)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    Position pos = trs.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("1.2.ε"));
  }

  @Test
  public void testLeftmostInnermostRedexIsEtaRedex() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    FunctionSymbol a = TermFactory.createConstant("a", type("A"));
    FunctionSymbol g = TermFactory.createConstant("g", type("A => A => A"));
    FunctionSymbol h = TermFactory.createConstant("h", type("(A => A) => A => A"));
    symbols.add(a);
    symbols.add(g);
    symbols.add(h);
    Variable z = TermFactory.createVar("Z", type("A => A"));
    Variable y = TermFactory.createVar("Y", type("A"));
    rules.add(RuleFactory.createRule(TermFactory.createApp(h, z, y), z.apply(y)));
    Alphabet alf = new Alphabet(symbols);
    TRS trswith = TRSFactory.createCFS(alf, rules, true);
    TRS trswithout = TRSFactory.createCFS(alf, rules, false);
    // rule: h(Z, Y) → Z(Y)

    Variable x = TermFactory.createBinder("x", type("A"));
    Term term = TermFactory.createApp(h,
      TermFactory.createAbstraction(x, TermFactory.createApp(g, a, x)),
      TermFactory.createApp(TermFactory.createAbstraction(x, x), a));
    // term: h(λx.g(a, x), (λx.x)(a))

    Position pos;
    pos = trswith.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("1.ε"));
    pos = trswithout.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("2.ε"));
  }

  @Test
  public void testLeftmostInnermostReduction() {
    TRS trs = createTermRewritingSystem(true);
    String str = "f(g(a, (λx::A.x)(b), a), λz.a)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("f(g(a, b, a), λz.a)"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("f(g(b, a, h(λz.z, b)), λz.a)"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("f(g(b, a, (λz.z)(b)), λz.a)"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("f(g(b, a, b), λz.a)"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term == null);
  }
}

