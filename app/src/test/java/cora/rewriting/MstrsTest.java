/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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

import java.util.ArrayList;
import java.util.TreeSet;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import static org.junit.jupiter.api.Assertions.*;

import cora.types.*;
import cora.terms.*;
import cora.terms.position.Position;
import cora.reader.CoraInputReader;

class MstrsTest {
  private Type type(String str) {
    try { return CoraInputReader.readType(str); }
    catch (Exception e) { System.out.println(e); return null; }
  }

  private TreeSet<FunctionSymbol> emptyPriv() { return new TreeSet<FunctionSymbol>(); }

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

  private TRS createTermRewritingSystem() {
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
    rules.add(new Rule(left1, right1));
      // f(x, a) -> x

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(x);
    args.add(x);
    args.add(b());
    Term left2 = TermFactory.createApp(g(), args);
    Term right2 = TermFactory.createApp(f(), b(), x);
    rules.add(new Rule(left2, right2));
      // g(x, x, b) -> f(b, x)

    return TRSFactory.createMSTRS(alf, rules, emptyPriv());
  }

  @Test
  public void testBasics() {
    TRS trs = createTermRewritingSystem();
    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).toString().equals("f(x, a) → x"));
    assertTrue(trs.queryRule(1).toString().equals("g(x, x, b) → f(b, x)"));
    assertTrue(trs.querySchemeCount() == 0);
    assertTrue(trs.lookupSymbol("f").equals(f()));
    assertTrue(trs.lookupSymbol("ff") == null);
  }

  @Test
  public void testPrivate() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());
    symbols.add(b());
    Alphabet alf = new Alphabet(symbols);

    ArrayList<Rule> rules = new ArrayList<Rule>();
    TreeSet<FunctionSymbol> priv = new TreeSet<FunctionSymbol>();
    priv.add(b());

    TRS trs = TRSFactory.createMSTRS(alf, rules, priv);
    assertFalse(trs.isPrivate(a()));
    assertTrue(trs.isPrivate(b()));
  }
  
  @Test
  public void testLeftmostInnermostRedex() {
    TRS trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), g(b, b, b)), b)";
    Term term = CoraInputReader.readTerm(str, trs);
    Position pos = trs.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("2.2.ε"));
  }

  @Test
  public void testLeftmostInnermostReduction() {
    TRS trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), g(b, b, b)), b)";
    Term term = CoraInputReader.readTerm(str, trs);
    String reduct = trs.leftmostInnermostReduce(term).toString();
    assertTrue(reduct.equals("g(f(a, b), f(g(a, b, a), f(b, b)), b)"));
  }

  @Test
  public void testLeftmostInnermostIrreducible() {
    TRS trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), x), b)";
    Term term = CoraInputReader.readTerm(str, trs);
    assertTrue(trs.leftmostInnermostReduce(term) == null);
  }
}

