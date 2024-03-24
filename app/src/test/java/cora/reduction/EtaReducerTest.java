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
import charlie.terms.*;

public class EtaReducerTest {
  @Test
  public void testBasicEtaReducer() {
    // λx.f(x) → f
    FunctionSymbol f = TermFactory.createConstant("f", 1);
    Variable x = TermFactory.createBinder("x", TypeFactory.defaultSort);
    Term s = TermFactory.createAbstraction(x, f.apply(x));
    EtaReducer eta = new EtaReducer();
    assertTrue(eta.applicable(s));
    Term t = eta.apply(s);
    assertTrue(t.equals(f));
  }

  @Test
  public void testEtaReducerAtHead() {
    // (λx.f(y, x))(a, b) → f(y, a, b)
    FunctionSymbol f = TermFactory.createConstant("f", 3);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    FunctionSymbol b = TermFactory.createConstant("b", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.defaultSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.defaultSort);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createApp(f, y, x));
    Term s = TermFactory.createApp(abs, a, b);
    EtaReducer eta = new EtaReducer();
    assertTrue(eta.applicable(s));
    Term t = eta.apply(s);
    assertTrue(t.toString().equals("f(y, a, b)"));
  }

  @Test
  public void testVariableOccursInHead() {
    // λx.(λy.f(x,y))(a, x)
    FunctionSymbol f = TermFactory.createConstant("f", 3);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.defaultSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.defaultSort);
    Term abs = TermFactory.createAbstraction(y, TermFactory.createApp(f, x, y));
      // λy.f(x,y)
    Term s = TermFactory.createAbstraction(x, TermFactory.createApp(abs, a, x));
    EtaReducer eta = new EtaReducer();
    assertFalse(eta.applicable(s));
    assertTrue(eta.apply(s) == null);
  }

  @Test
  public void testVariableOccursInEarlierArgument() {
    // (λx.f(y, x, x))(a)
    FunctionSymbol f = TermFactory.createConstant("f", 3);
    FunctionSymbol a = TermFactory.createConstant("a", 0);
    Variable x = TermFactory.createBinder("x", TypeFactory.defaultSort);
    Variable y = TermFactory.createBinder("y", TypeFactory.defaultSort);
    Term abs = TermFactory.createAbstraction(x, TermFactory.createApp(f, y, x).apply(x));
    Term s = abs.apply(a);
    EtaReducer eta = new EtaReducer();
    assertFalse(eta.applicable(s));
    assertTrue(eta.apply(s) == null);
  }
}

