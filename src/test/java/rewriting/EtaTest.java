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

public class EtaTest {
  @Test
  public void testBasicEta() {
    // λx.f(x) → f
    FunctionSymbol f = TermFactory.createConstant("f", 1);
    Variable x = TermFactory.createBinder("x", TypeFactory.unitSort);
    Term s = TermFactory.createAbstraction(x, f.apply(x));
    Eta eta = new Eta();
    assertTrue(eta.applicable(s));
    Term t = eta.apply(s);
    assertTrue(t.equals(f));
  }

  @Test
  public void testEtaAtHead() {
    // (λx.f(y, x))(a, b) → f(y, a, b)
    FunctionSymbol f = TermFactory.createConstant("f", 3);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.unitSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.unitSort);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createApp(f, y, x));
    Term s = TermFactory.createApp(abs, a, b);
    Eta eta = new Eta();
    assertTrue(eta.applicable(s));
    Term t = eta.apply(s);
    assertTrue(t.toString().equals("f(y, a, b)"));
  }

  @Test
  public void testVariableOccursInHead() {
    // λx.(λy.f(x,y))(a, x)
    FunctionSymbol f = TermFactory.createConstant("f", 3);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.unitSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.unitSort);
    Term abs = TermFactory.createAbstraction(y, TermFactory.createApp(f, x, y));
      // λy.f(x,y)
    Term s = TermFactory.createAbstraction(x, TermFactory.createApp(abs, a, x));
    Eta eta = new Eta();
    assertFalse(eta.applicable(s));
    assertTrue(eta.apply(s) == null);
  }

  @Test
  public void testVariableOccursInEarlierArgument() {
    // (λx.f(y, x, x))(a)
    FunctionSymbol f = TermFactory.createConstant("f", 3);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.unitSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.unitSort);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createApp(f, y, x).apply(x));
    Term s = abs.apply(a);
    Eta eta = new Eta();
    assertFalse(eta.applicable(s));
    assertTrue(eta.apply(s) == null);
  }
}

