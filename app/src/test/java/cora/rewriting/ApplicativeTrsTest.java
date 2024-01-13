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

package cora.rewriting;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.IllegalRuleError;
import cora.exceptions.NullInitialisationError;
import cora.types.*;
import cora.terms.*;
import cora.terms.position.Position;
import cora.reader.CoraInputReader;

public class ApplicativeTrsTest {
  private Type type(String str) {
    return CoraInputReader.readType(str);
  }

  private TRS createTermRewritingSystem() {
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
    rules.add(RuleFactory.createApplicativeRule(
      TermFactory.createApp(f, g.apply(x), a), TermFactory.createApp(g, a, x)));
      // f(g(x), a) -> g(a, x) with g :: A -> B -> A -> B
    rules.add(RuleFactory.createApplicativeRule(
      TermFactory.createApp(g, y.apply(x), x).apply(z),
      TermFactory.createApp(g, z, x).apply(y.apply(a))));
      // g(y(x), x, z) -> g(z, x, y(a))
    return TRSFactory.createApplicativeTRS(new Alphabet(symbols), rules);
  }

  @Test
  public void testCreateApplicativeTRS() {
    TRS trs = createTermRewritingSystem();
    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).toString().equals("f(g(x), a) → g(a, x)"));
    assertTrue(trs.queryRule(1).toString().equals("g(y(x), x, z) → g(z, x, y(a))"));
    assertTrue(trs.querySchemeCount() == 0);
    assertTrue(trs.lookupSymbol("f").equals(
      TermFactory.createConstant("f", type("(A → A → B) → A → A → B"))));
    assertTrue(trs.lookupSymbol("h") == null);
  }

  @Test(expected = IllegalRuleError.class)
  public void testFailToCreateApplicativeTRS() {
    // fail by including a non-applicative rule
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createBinder("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    symbols.add(f);
    rules.add(RuleFactory.createRule(TermFactory.createApp(f, x, y), y));
    TRSFactory.createApplicativeTRS(new Alphabet(symbols), rules);
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateApplicativeTRSWithNullAlphabet() {
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    rules.add(RuleFactory.createRule(TermFactory.createApp(f, x, y), y));
    TRSFactory.createApplicativeTRS(null, rules);
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateApplicativeTRSWithNullRules() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    symbols.add(f);
    TRSFactory.createApplicativeTRS(new Alphabet(symbols), null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateApplicativeTRSWithNullRule() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    symbols.add(f);
    rules.add(RuleFactory.createRule(TermFactory.createApp(f, x, y), y));
    rules.add(null);
    TRSFactory.createApplicativeTRS(new Alphabet(symbols), rules);
  }

  @Test
  public void testExpandApplicativeTRSAfterCreationDoesNothing() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    symbols.add(f);
    rules.add(RuleFactory.createRule(TermFactory.createApp(f, x, y), y));
    TRS trs = TRSFactory.createApplicativeTRS(new Alphabet(symbols), rules);
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
  public void testLeftmostInnermostRedex() {
    // note that although the rule f(g(x), a) -> g(a, x) is *technically* on the
    // left of the redex g(j(a, b), b, a), we consider only maximally applied
    // subterms, so the innermost redex takes precedence
    TRS trs = createTermRewritingSystem();
    String str = "f(g(a), a, i(g(j(a,b), b, a)))";
    Term term = CoraInputReader.readTerm(str, trs);
    Position pos = trs.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("3.1.ε"));
  }

  @Test
  public void testLeftmostInnermostReduction() {
    TRS trs = createTermRewritingSystem();
    String str = "f(g(a), a, i(g(j(a,b), b, a)))";
    Term term = CoraInputReader.readTerm(str, trs);
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("f(g(a), a, i(g(a, b, j(a, a))))"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term.toString().equals("g(a, a, i(g(a, b, j(a, a))))"));
    term = trs.leftmostInnermostReduce(term);
    assertTrue(term == null);
  }
}

