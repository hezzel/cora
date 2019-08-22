/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Position;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.UserDefinedAlphabet;
import cora.rewriting.SimpleRule;
import cora.rewriting.TermRewritingSystem;
import cora.parsers.CoraInputReader;

public class TrsTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  private FunctionSymbol a() {
    return new UserDefinedSymbol("a", baseType("o"));
  }

  private FunctionSymbol b() {
    return new UserDefinedSymbol("b", baseType("o"));
  }

  private FunctionSymbol f() {
    Type type =  new ArrowType(baseType("o"), new ArrowType(baseType("o"), baseType("o")));
    return new UserDefinedSymbol("f", type);
  }

  private FunctionSymbol g() {
    Type oo = baseType("o");
    Type type = new ArrowType(oo, new ArrowType(oo, new ArrowType(oo, oo)));
    return new UserDefinedSymbol("g", type);
  }

  public TermRewritingSystem createTermRewritingSystem() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(a());
    symbols.add(b());
    symbols.add(f());
    symbols.add(g());
    UserDefinedAlphabet alf = new UserDefinedAlphabet(symbols);

    ArrayList<Rule> rules = new ArrayList<Rule>();
    Var x = new Var("x", baseType("o"));
    Term left1 = new FunctionalTerm(f(), x, new FunctionalTerm(a()));
    Term right1 = x;
    rules.add(new SimpleRule(left1, right1));
      // f(x, a) -> x

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(x);
    args.add(x);
    args.add(new FunctionalTerm(b()));
    Term left2 = new FunctionalTerm(g(), args);
    Term right2 = new FunctionalTerm(f(), new FunctionalTerm(b()), x);
    rules.add(new SimpleRule(left2, right2));
      // g(x, x, b) -> f(b, x)

    return new TermRewritingSystem(alf, rules);
  }

  @Test
  public void testLeftmostInnermostRedex() {
    TermRewritingSystem trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), g(b, b, b)), b)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    Position pos = trs.leftmostInnermostRedexPosition(term);
    assertTrue(pos.toString().equals("2.2.ε"));
  }

  @Test
  public void testLeftmostInnermostReduction() {
    TermRewritingSystem trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), g(b, b, b)), b)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    String reduct = trs.leftmostInnermostReduce(term).toString();
    assertTrue(reduct.equals("g(f(a, b), f(g(a, b, a), f(b, b)), b)"));
  }

  @Test
  public void testLeftmostInnermostIrreducible() {
    TermRewritingSystem trs = createTermRewritingSystem();
    String str = "g(f(a, b), f(g(a, b, a), x), b)";
    Term term = CoraInputReader.readTermFromString(str, trs);
    assertTrue(trs.leftmostInnermostReduce(term) == null);
  }
}

