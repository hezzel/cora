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

package cora.trs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.ArrayList;

import cora.exceptions.IllegalRuleError;
import cora.exceptions.NullInitialisationError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.*;
import cora.reader.CoraInputReader;

public class TrsFactoryTrsCreationTest {
  private Type type(String text) {
    return CoraInputReader.readType(text);
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
}

