/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

import charlie.exceptions.IllegalRuleException;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.parser.CoraParser;
import charlie.terms.*;

public class TrsFactoryRuleCreationTest {
  private Type type(String text) {
    return CoraParser.readType(text);
  }

  private FunctionSymbol makeConstant(String name, Type type) {
    return TermFactory.createConstant(name, type);
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = TypeFactory.createArrow(arg.queryType(), output);
    FunctionSymbol f = TermFactory.createConstant(name, arrtype);
    return f.apply(arg);
  }

  @Test
  public void testLeftNullCreation() {
    assertThrows(NullStorageException.class, () ->
      TrsFactory.createRule(makeConstant("a", type("b")), null, TrsFactory.MSTRS));
  }

  @Test
  public void testRightNullCreation() {
    assertThrows(NullStorageException.class, () ->
      TrsFactory.createRule(null, makeConstant("a", type("b")), TrsFactory.MSTRS));
  }

  @Test
  public void testIlltypedRule() {
    Variable x = TermFactory.createVar("x", type("a"));
    Term left = unaryTerm("id", type("b"), x);
    assertThrows(TypingException.class, () -> TrsFactory.createRule(left, x, TrsFactory.MSTRS));
  }

  @Test
  public void testVariableLeft() {
    Variable x = TermFactory.createVar("x", type("a"));
    Term right = unaryTerm("id", type("a"), x);
    assertThrows(IllegalRuleException.class,
      () -> TrsFactory.createRule(x, right, TrsFactory.MSTRS));
  }

  @Test
  public void testNotFirstOrder() {
    Type t = type("a -> b");
    Variable x = TermFactory.createVar("x", t);
    Term left = unaryTerm("id", t, x);
    assertThrows(IllegalRuleException.class,
      () -> TrsFactory.createRule(left, x, TrsFactory.MSTRS));
  }

  @Test
  public void testFreshVariableInRhs() {
    Variable x = TermFactory.createVar("x", type("Bool"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("z", type("Int"));
    FunctionSymbol f = TermFactory.createConstant("f", type("Bool -> Int -> o"));
    Term left = TermFactory.createApp(f, x, y);
    Term right = TermFactory.createApp(f, x, z);
    // this is not allowed for an MSTRS
    assertThrows(IllegalRuleException.class,
      () -> TrsFactory.createRule(left, right, TrsFactory.MSTRS));
    // it's also disallowed for an LCTRS
    assertThrows(IllegalRuleException.class,
      () -> TrsFactory.createRule(left, right, TrsFactory.LCTRS));
    // but it IS allowed if the fresh variable occurs in the constraint
    Term constraint = TheoryFactory.greaterSymbol.apply(y).apply(z);
    TrsFactory.createRule(left, right, constraint, TrsFactory.LCTRS);
    // and it is allowed even without constraint in a CORA-TRS
    TrsFactory.createRule(left, right, TrsFactory.CORA);
  }

  @Test
  public void testApplicativeRuleNotApplicative() {
    // a → g(λz.z)
    Term a = makeConstant("a", type("o"));
    Term g = makeConstant("g", type("(a -> a) -> o"));
    Variable z = TermFactory.createBinder("z", type("a"));
    assertThrows(IllegalRuleException.class, () ->
      TrsFactory.createRule(a, g.apply(TermFactory.createAbstraction(z, z)), TrsFactory.STRS));
  }

  @Test
  public void testCFSRuleWithMetaVariables() {
    // f(λx.Z⟨x⟩) → a
    Term f = TermFactory.createConstant("f", type("(o → o) → o"));
    Variable x = TermFactory.createBinder("x", type("o"));
    MetaVariable z = TermFactory.createMetaVar("Z", type("o → o"), 1);
    Term left = f.apply(TermFactory.createAbstraction(x, TermFactory.createMeta(z, x)));
    Term right = makeConstant("a", type("o"));
    assertThrows(IllegalRuleException.class,
      () -> TrsFactory.createRule(left, right, TrsFactory.CFS));
  }

  @Test
  public void testNonPatternRule() {
    // f(λx.Z[b]) → a
    Term f = TermFactory.createConstant("f", type("(o → o) → o"));
    Variable x = TermFactory.createBinder("x", type("o"));
    MetaVariable z = TermFactory.createMetaVar("Z", type("o → o"), 1);
    Term a = makeConstant("a", type("o"));
    Term left = f.apply(TermFactory.createAbstraction(x, TermFactory.createMeta(z, a)));
    assertThrows(IllegalRuleException.class,
      () -> TrsFactory.createRule(left, a, TrsFactory.AMS));
  }

  @Test
  public void testRuleWithBinder() {
    Variable x = TermFactory.createBinder("x", type("a"));
    Variable y = TermFactory.createVar("y", type("b"));
    FunctionSymbol f = TermFactory.createConstant("f", type("a → b → b"));
    assertThrows(IllegalRuleException.class,
      () -> new Rule(TermFactory.createApp(f, x, y), y));
  }

  @Test
  public void testBasics() {
    Variable x = TermFactory.createVar("x", type("a"));
    Term left = unaryTerm("id", type("a"), x);
    Rule rule = TrsFactory.createRule(left, x, TrsFactory.AMS);
    assertTrue(rule.queryLeftSide().equals(left));
    assertTrue(rule.queryRightSide().equals(x));
    assertTrue(rule.queryType().equals(type("a")));
    assertTrue(rule.toString().equals("id(x) → x"));
    assertTrue(rule.isApplicative());
    assertTrue(rule.isFirstOrder());
  }
}

