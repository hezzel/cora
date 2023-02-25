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
import cora.types.TypeFactory;
import cora.terms.*;

public class BetaTest {
  @Test
  public void testBasicBeta() {
    // (λx.f(x,y))(a) → f(a, y)
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.unitSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.unitSort);
    Term s = TermFactory.createApp(TermFactory.createAbstraction(x,
      TermFactory.createApp(f, x, y)), a);

    Beta beta = new Beta();
    assertTrue(beta.applicable(s));
    Term t = beta.apply(s);
    assertTrue(t.toString().equals("f(a, y)"));
  }

  @Test
  public void testBetaAtHead() {
    // (λx.λy.f(x, f(y, x)))(a, b) → (λy.f(a, f(y, a)))(b)
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.unitSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.unitSort);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createAbstraction(y,
      TermFactory.createApp(f, x, TermFactory.createApp(f, y, x))));
    Term s = TermFactory.createApp(abs, a, b);

    Beta beta = new Beta();
    assertTrue(beta.applicable(s));
    Term t = beta.apply(s);
    assertTrue(t.toString().equals("(λy.f(a, f(y, a)))(b)"));
  }

  @Test
  public void testBetaEta() {
    // (λx.f(y,x))(f(z,z)) → f(y, f(z, z))
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    Variable x = TermFactory.createBinder("x", TypeFactory.unitSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.unitSort);
    Variable z = TermFactory.createBinder("z", TypeFactory.unitSort);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createApp(f, y, x));
    Term s = TermFactory.createApp(abs, TermFactory.createApp(f, z, z));

    Beta beta = new Beta();
    assertTrue(beta.applicable(s));
    Term t = beta.apply(s);
    assertTrue(t.toString().equals("f(y, f(z, z))"));
  }

  @Test
  public void testAbstractionNoBeta() {
    // λx.f(x)
    FunctionSymbol f = TermFactory.createConstant("f", 1);
    Variable x = TermFactory.createBinder("x", TypeFactory.unitSort);
    Term s = TermFactory.createAbstraction(x, TermFactory.createApp(f, x));
    Beta beta = new Beta();
    assertFalse(beta.applicable(s));
    assertTrue(beta.apply(s) == null);
  }

  @Test
  public void testApplicationNoBeta() {
    // f(a, b)
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    Term s = TermFactory.createApp(f, a, b);
    Beta beta = new Beta();
    assertFalse(beta.applicable(s));
    assertTrue(beta.apply(s) == null);
  }
}

