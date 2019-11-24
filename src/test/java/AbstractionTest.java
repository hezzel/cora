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
import java.util.List;
import java.util.ArrayList;
import cora.exceptions.IndexingError;
import cora.exceptions.IllegalTermError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;
import cora.terms.positions.*;

public class AbstractionTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  private Term constantTerm(String name, Type type) {
    return new Constant(name, type);
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = new ArrowType(arg.queryType(), output);
    FunctionSymbol f = new Constant(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  private Variable createBinder(String name, String type) {
    return new BinderVariable(name, baseType(type));
  }

  private Abstraction exampleAbstraction(Variable x) {
    // build: λx.f(x, g(c)) with c : Int, g(c) : Bool and f(x, g(c)) : A
    Constant f =
      new Constant("f", new ArrowType(baseType("Int"), arrowType("Bool", "A")));
    Constant g =
      new Constant("g", arrowType("Int", "Bool"));
    Term fxgc = new FunctionalTerm(f, x, new FunctionalTerm(g, constantTerm("c", baseType("Int"))));
    return new Abstraction(x, fxgc);
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateWithNullBinder() {
    Abstraction abs = new Abstraction(null, constantTerm("a", baseType("b")));
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateWithNullSubterm() {
    Abstraction abs = new Abstraction(createBinder("x", "o"), null);
  }

  @Test(expected = java.lang.Error.class)
  public void testCreationWithFreeVariable() {
    Variable x = new Var("x", baseType("Int"));
    Abstraction abs = exampleAbstraction(x);
  }

  @Test(expected = IndexingError.class)
  public void testImmediateSubtermTooLarge() {
    Abstraction abs = exampleAbstraction(createBinder("x", "Int"));
    abs.queryImmediateSubterm(1);
  }

  @Test(expected = IndexingError.class)
  public void testImmediateSubtermTooSmall() {
    Abstraction abs = exampleAbstraction(createBinder("x", "Int"));
    abs.queryImmediateSubterm(-1);
  }

  @Test(expected = IndexingError.class)
  public void testQueryForHeadSubterm() {
    Abstraction abs = exampleAbstraction(createBinder("x", "Int"));
    abs.queryImmediateHeadSubterm(1);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testQueryRoot() {
    Abstraction abs = exampleAbstraction(createBinder("x", "Int"));
    abs.queryRoot();
  }

  @Test
  public void testBasicsWithSingleVar() {
    // build: λx:Int.f(x, g(c)) with c : Int, g(c) : Bool and f(x, g(c)) : A
    Variable x = createBinder("x", "Int");
    Abstraction abs = exampleAbstraction(x);

    assertFalse(abs.isVariable());
    assertFalse(abs.isConstant());
    assertFalse(abs.isFunctionalTerm());
    assertFalse(abs.isVarTerm());
    assertTrue(abs.isAbstraction());
    assertTrue(abs.isPattern());
    assertFalse(abs.isFirstOrder());

    assertTrue(abs.queryType().equals(arrowType("Int", "A")));
    assertEquals(1, abs.numberImmediateSubterms());
    assertTrue(abs.queryImmediateSubterm(0).toString().equals("f(x, g(c))"));
    assertTrue(abs.queryImmediateHeadSubterm(0).equals(abs));
    assertTrue(abs.queryVariable().equals(x));
    System.out.println("abs = " + abs.toString());
    assertTrue(abs.toString().equals("λx.f(x, g(c))"));
  }

  @Test
  public void testBasicsWithDoubleVar() {
    // build: λx y.f(y, g(c))
    Variable x = createBinder("x", "Bool");
    Variable y = createBinder("y", "Int");
    Abstraction abs = new Abstraction(x, exampleAbstraction(y));

    assertTrue(abs.isAbstraction());
    assertTrue(abs.queryType().equals(new ArrowType(baseType("Bool"), arrowType("Int", "A"))));
    assertEquals(1, abs.numberImmediateSubterms());
    assertTrue(abs.queryImmediateSubterm(0).equals(exampleAbstraction(y)));
    assertTrue(abs.queryImmediateHeadSubterm(0).equals(abs));
    assertTrue(abs.queryVariable().equals(x));
  }

  @Test
  public void testPattern() {
    Variable x = new BinderVariable("x", arrowType("Int", "Int"));
    Abstraction abs1 = new Abstraction(x, x);
    assertTrue(abs1.isPattern());

    Abstraction abs2 = new Abstraction(x, new VarTerm(x, constantTerm("37", baseType("Int"))));
    assertTrue(abs2.isPattern());

    Variable y = new Var("y", arrowType("Bool", "Bool"));
    Variable z = new BinderVariable("z", baseType("Bool"));
    Abstraction abs3 = new Abstraction(z, new VarTerm(y, z));
    assertTrue(abs3.isPattern());

    Abstraction abs4 = new Abstraction(x, new VarTerm(y, z));
    assertTrue(abs4.isPattern());

    Abstraction abs5 = new Abstraction(x, new VarTerm(y, constantTerm("true", baseType("Bool"))));
    assertFalse(abs5.isPattern());
  }
}

