/**************************************************************************************************
 Copyright 2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.theory;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;

import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.*;

class TheoryCheckTest {
  @Test
  public void testConstant() {
    FunctionSymbol f = TermFactory.createConstant("0", TypeFactory.intSort);
    assertFalse(Theory.isTheory(f));
    assertFalse(Theory.isTheory((Term)f));
    assertFalse(Theory.isValue(f));
    assertTrue(Theory.toValue(f) == null);
  }

  @Test
  public void testVariable() {
    Variable x = TermFactory.createVar("x", TypeFactory.createSort("aa"));
    Variable y = TermFactory.createVar("y",
      TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.stringSort));
    assertFalse(Theory.isTheory(x));
    assertTrue(Theory.isTheory(y));
    assertFalse(Theory.isValue(y));
    assertTrue(Theory.toValue(y) == null);
  }
  @Test
  public void testBinder() {
    Variable x = TermFactory.createBinder("x", TypeFactory.createSort("aa"));
    Variable y = TermFactory.createBinder("y", TypeFactory.boolSort);
    assertFalse(Theory.isTheory(x));
    assertTrue(Theory.isTheory(y));
    assertFalse(Theory.isValue(y));
    assertTrue(Theory.toValue(y) == null);
  }

  @Test
  public void testAbstraction() {
    // λx::Int.x + 1
    Variable x = TermFactory.createBinder("x", TypeFactory.intSort);
    Term abs = TermFactory.createAbstraction(x,
      TermFactory.createApp(TheoryFactory.plusSymbol, x, new IntegerValue(1)));
    assertEquals("λx.x + 1", abs.toString());
    assertTrue(Theory.isTheory(abs));
    assertFalse(Theory.isValue(abs));
    assertNull(Theory.toValue(abs));

    // λy::o.0
    Variable y = TermFactory.createBinder("y", TypeFactory.defaultSort);
    abs = TermFactory.createAbstraction(y, new IntegerValue(0));
    assertFalse(Theory.isTheory(abs));
  }

  @Test
  public void testApplication() {
    // +(x(0), y(z))
    Term zero = new IntegerValue(0);
    Term x =
      TermFactory.createVar("x", TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.intSort));
    Term y = TermFactory.createBinder("y", TypeFactory.intSort);
    Term t = TermFactory.createApp(TheoryFactory.plusSymbol, x.apply(zero), y);
    assertTrue(Theory.isTheory(t));
    assertFalse(Theory.isValue(t));
    assertTrue(Theory.toValue(t) == null);
    // z(0) with z :: Int → a
    Variable z = TermFactory.createVar("z",
      TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.createSort("a")));
    t = z.apply(zero);
    assertFalse(Theory.isTheory(t));
    // +(1, 2)
    t = TermFactory.createApp(TheoryFactory.plusSymbol, new IntegerValue(1), new IntegerValue(2));
    assertTrue(Theory.isTheory(t));
    assertFalse(Theory.isValue(t));
    assertTrue(Theory.toValue(t) == null);
  }

  private Term makeMeta(String name, Term arg, Type output) {
    MetaVariable z = TermFactory.createMetaVar(name, List.of(arg.queryType()), output);
    return TermFactory.createMeta(z, arg);
  }

  @Test
  public void testMetaApplication() {
    // X[0] with X :: Int → a
    Term s = makeMeta("X", new IntegerValue(0), TypeFactory.createSort("a"));
    assertFalse(Theory.isTheory(s));
    assertFalse(Theory.isValue(s));

    // Y[o] with Y :: Int → Int but o not a theory term
    s = makeMeta("Y", TermFactory.createConstant("o", TypeFactory.intSort), TypeFactory.intSort);
    assertFalse(Theory.isTheory(s));
    assertTrue(Theory.toValue(s) == null);

    // Z[λx.x,y] with Z :: (Int → Int) → String → Bool
    Variable x = TermFactory.createBinder("x", TypeFactory.intSort);
    Variable y = TermFactory.createVar("y", TypeFactory.stringSort);
    Term abs = TermFactory.createAbstraction(x, x);

    MetaVariable z =
      TermFactory.createMetaVar("Z", abs.queryType(), y.queryType(), TypeFactory.boolSort);
    s = TermFactory.createMeta(z, abs, y);
    assertFalse(Theory.isTheory(s));
    assertFalse(Theory.isValue(s));
    assertTrue(Theory.toValue(s) == null);
  }
}
