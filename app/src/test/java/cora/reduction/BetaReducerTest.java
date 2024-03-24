/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

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

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.types.TypeFactory;
import cora.terms.*;

public class BetaReducerTest {
  @Test
  public void testBasicBetaReducer() {
    // (λx.f(x,y))(a) → f(a, y)
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.defaultSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.defaultSort);
    Term s = TermFactory.createApp(TermFactory.createAbstraction(x,
      TermFactory.createApp(f, x, y)), a);

    BetaReducer beta = new BetaReducer();
    assertTrue(beta.applicable(s));
    Term t = beta.apply(s);
    assertTrue(t.toString().equals("f(a, y)"));
  }

  @Test
  public void testBetaReducerAtHead() {
    // (λx.λy.f(x, f(y, x)))(a, b) → (λy.f(a, f(y, a)))(b)
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.defaultSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.defaultSort);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createAbstraction(y,
      TermFactory.createApp(f, x, TermFactory.createApp(f, y, x))));
    Term s = TermFactory.createApp(abs, a, b);

    BetaReducer beta = new BetaReducer();
    assertTrue(beta.applicable(s));
    Term t = beta.apply(s);
    assertTrue(t.toString().equals("(λy.f(a, f(y, a)))(b)"));
  }

  @Test
  public void testBetaReducerEta() {
    // (λx.f(y,x))(f(z,z)) → f(y, f(z, z))
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    Variable x = TermFactory.createBinder("x", TypeFactory.defaultSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.defaultSort);
    Variable z = TermFactory.createBinder("z", TypeFactory.defaultSort);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createApp(f, y, x));
    Term s = TermFactory.createApp(abs, TermFactory.createApp(f, z, z));

    BetaReducer beta = new BetaReducer();
    assertTrue(beta.applicable(s));
    Term t = beta.apply(s);
    assertTrue(t.toString().equals("f(y, f(z, z))"));
  }

  @Test
  public void testAbstractionNoBetaReducer() {
    // λx.f(x)
    FunctionSymbol f = TermFactory.createConstant("f", 1);
    Variable x = TermFactory.createBinder("x", TypeFactory.defaultSort);
    Term s = TermFactory.createAbstraction(x, TermFactory.createApp(f, x));
    BetaReducer beta = new BetaReducer();
    assertFalse(beta.applicable(s));
    assertTrue(beta.apply(s) == null);
  }

  @Test
  public void testApplicationNoBetaReducer() {
    // f(a, b)
    FunctionSymbol f = TermFactory.createConstant("f", 2);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    Term s = TermFactory.createApp(f, a, b);
    BetaReducer beta = new BetaReducer();
    assertFalse(beta.applicable(s));
    assertTrue(beta.apply(s) == null);
  }
}

