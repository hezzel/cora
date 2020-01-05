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

  @Test(expected = IllegalTermError.class)
  public void testBindervarReuseIllegal() {
    Variable x = createBinder("x", "o");
    Constant f =
      new Constant("f", new ArrowType(arrowType("o", "o"), arrowType("o", "o")));
    Term fxlambdaxx = new FunctionalTerm(f, new Abstraction(x,x), x);
  }

  @Test(expected = java.lang.Error.class)
  public void testDoubleAbstractionWithSameVariable() {
    Variable x = createBinder("x", "o");
    Abstraction lambdaxxx = new Abstraction(x, new Abstraction(x, x));
  }

  @Test
  public void testVars() {
    // λx:o.z(λy:o.y, a)
    Variable x = createBinder("x", "o");
    Variable y = createBinder("o", "o");
    Variable z = new Var("z", new ArrowType(arrowType("o", "o"), arrowType("o", "o")));
    Term a = constantTerm("a", baseType("o"));
    Abstraction abs = new Abstraction(x, new VarTerm(z, new Abstraction(y,y), a));

    assertTrue(abs.freeVars().contains(z));
    assertTrue(abs.freeVars().size() == 1);
    assertTrue(abs.boundVars().contains(x));
    assertTrue(abs.boundVars().contains(y));
    assertTrue(abs.boundVars().size() == 2);
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
  public void testPositions() {
    // build: λx:Int.f(x, g(c)) with c : Int, g(c) : Bool and f(x, g(c)) : A 
    Variable x = createBinder("x", "Int");
    Abstraction abs = exampleAbstraction(x);
    List<Position> posses = abs.queryAllPositions();
    assertTrue(posses.size() == 5); 
    assertTrue(posses.get(0).toString().equals("0.1.ε"));
    assertTrue(posses.get(1).toString().equals("0.2.1.ε"));
    assertTrue(posses.get(2).toString().equals("0.2.ε"));
    assertTrue(posses.get(3).equals(new AbstractionPosition(new EmptyPosition())));
    assertTrue(posses.get(4).equals(new EmptyPosition()));
  }

  @Test
  public void testSubtermsAtPositions() {
    // build: λx:Int.f(x, g(c)) with c : Int, g(c) : Bool and f(x, g(c)) : A 
    Variable x = createBinder("x", "Int");
    Abstraction abs = exampleAbstraction(x);

    Position pos = new EmptyPosition();   // ε
    assertTrue(abs.querySubterm(pos).equals(abs));
    pos = new AbstractionPosition(new EmptyPosition());   // 0.ε 
    assertTrue(abs.querySubterm(pos).toString().equals("f(x, g(c))"));
    pos = new AbstractionPosition(new ArgumentPosition(1, new EmptyPosition()));
    assertTrue(abs.querySubterm(pos).equals(x));
  }

  @Test
  public void testReplaceSubterm() {
    // create relevant function symbols and variables
    Variable x = createBinder("x", "Int");
    Constant f =
      new Constant("f", new ArrowType(baseType("Int"), arrowType("Int", "Int")));
    Constant g =
      new Constant("g", arrowType("Int", "Int"));
    Constant c =
      new Constant("c", baseType("Int"));

    // build: λx.f(x, g(c))
    Term gc = new FunctionalTerm(g, c);
    Term fxgc = new FunctionalTerm(f, x, gc);
    Term abs1 = new Abstraction(x, fxgc);

    // build: λx:Int.f(x, x)
    Term abs2 = new Abstraction(x, new FunctionalTerm(f, x, x));

    // build: λx:Int.f(f(x, g(c)), g(x))
    Term abs3 = new Abstraction(x, new FunctionalTerm(f, fxgc, gc));

    Position pos = new AbstractionPosition(new ArgumentPosition(2, new EmptyPosition()));
    assertTrue(abs1.replaceSubterm(pos, x).equals(abs2));

    pos = new AbstractionPosition(new ArgumentPosition(1, new EmptyPosition()));
    Term tmp = abs1.replaceSubterm(pos, fxgc);
    pos = new AbstractionPosition(new ArgumentPosition(1, new ArgumentPosition(1,
            new EmptyPosition())));
    assertTrue(tmp.replaceSubterm(pos, x).equals(abs3));

    Term aterm = constantTerm("a", arrowType("Int", "Int"));
    assertTrue(abs1.replaceSubterm(new EmptyPosition(), aterm).equals(aterm));
  }

  @Test(expected = TypingError.class)
  public void testReplaceSubtermIncorectTypeHead() {
    Variable x = createBinder("x", "Int");
    Abstraction abs = exampleAbstraction(x);
    Term aterm = constantTerm("a", arrowType("Int", "Int"));
    abs.replaceSubterm(new EmptyPosition(), aterm);
  }

  @Test(expected = TypingError.class)
  public void testReplaceSubtermIncorectTypeSubterm() {
    Variable x = createBinder("x", "Int");
    Abstraction abs = exampleAbstraction(x);
    Term aterm = constantTerm("a", baseType("Int"));
    abs.replaceSubterm(new AbstractionPosition(new EmptyPosition()), aterm);
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

  @Test
  public void testObviousEquality() {
    Variable x = createBinder("x", "Int");
    Abstraction abs1 = exampleAbstraction(x);
    Abstraction abs2 = exampleAbstraction(x);
    assertTrue(abs1.equals(abs2));
  }

  @Test
  public void testObviousInequality() {
    Variable x = createBinder("x", "o");
    Variable y = createBinder("y", "o");
    Constant f =
      new Constant("f", new ArrowType(baseType("o"), arrowType("o", "o")));
    Term fxy = new FunctionalTerm(f, x, y);
    Term abs1 = new Abstraction(x, fxy);
    Term abs2 = new Abstraction(y, fxy);

    assertFalse(abs1.equals(abs2));
  }

  @Test
  public void testSimpleAlphaEquivalence() {
    Variable x = createBinder("x", "o");
    Variable y = createBinder("y", "o");
    Constant f =
      new Constant("f", new ArrowType(baseType("o"), arrowType("o", "o")));
    Term a = constantTerm("a", baseType("o"));
    Term fxa = new FunctionalTerm(f, x, a);
    Term fya = new FunctionalTerm(f, y, a);
    Term abs1 = new Abstraction(x, fxa);
    Term abs2 = new Abstraction(y, fya);

    assertTrue(abs1.equals(abs2));
  }

  @Test
  public void testSwitchingAlphaEquivalence() {
    Variable x = createBinder("x", "o");
    Variable y = createBinder("y", "o");
    Constant f = new Constant("f", new ArrowType(baseType("o"), arrowType("o", "o")));

    // λxy.f(x,f(x,y))
    Term fxy = new FunctionalTerm(f, x, y);
    Term abs1 = new Abstraction(x, new Abstraction(y, new FunctionalTerm(f, x, fxy)));
    // λyx.f(y,f(y,x))
    Term fyx = new FunctionalTerm(f, y, x);
    Term abs2 = new Abstraction(y, new Abstraction(x, new FunctionalTerm(f, y, fyx)));

    assertTrue(abs1.equals(abs2));

    Term abs3 = new Abstraction(y, new Abstraction(x, new FunctionalTerm(f, fyx, y)));
    assertFalse(abs1.equals(abs3));
  }

  @Test
  public void testAlphaEquivalenceWithDifferentlyTypedBinders() {
    Variable x = createBinder("x", "a");
    Variable y = createBinder("y", "b");
    Variable z = createBinder("z", "b");
    Abstraction abs1 = new Abstraction(x, x);
    Abstraction abs2 = new Abstraction(y, y);
    Abstraction abs3 = new Abstraction(z, z);

    assertFalse(abs1.equals(abs2));
    assertTrue(abs2.equals(abs3));
  }

  @Test
  public void testNonEquivalenceWhereOnlyOneIsBound() {
    Variable x = createBinder("x", "a");
    Variable y = createBinder("y", "b");
    Abstraction abs1 = new Abstraction(x, x);
    Abstraction abs2 = new Abstraction(x, y);

    assertFalse(abs1.equals(abs2));
    assertFalse(abs2.equals(abs1));
  }

  @Test
  public void testSingleApplication() {
    // λx:o.f(x, y)
    Variable x = createBinder("x", "o");
    Variable y = createBinder("y", "o");
    Constant f = 
      new Constant("f", new ArrowType(baseType("o"), arrowType("o", "o")));
    Term fxy = new FunctionalTerm(f, x, y); 
    Term abs = new Abstraction(x, fxy);

    // g(a)
    Constant g = new Constant("g", arrowType("asort", "o"));
    Term ga = new FunctionalTerm(g, constantTerm("a", baseType("asort")));

    // f(g(a), y)
    Term fgay = new FunctionalTerm(f, ga, y); 

    assertTrue(abs.apply(ga).equals(fgay));
  }

  @Test
  public void testMultipApplication() {
    // λx:o -> o -> o.λy:o.x(f(y,y))
    Variable x = new BinderVariable("x", new ArrowType(baseType("o"), arrowType("o", "o")));
    Variable y = createBinder("y", "o");
    Constant f =
      new Constant("f", new ArrowType(baseType("o"), arrowType("o", "o")));
    Term fyy = new FunctionalTerm(f, y, y);
    Term xfyy = new VarTerm(x, fyy);      // note that this has type o -> o
    Term complete = new Abstraction(x, new Abstraction(y, xfyy));

    // applying it on [a,b,c]
    ArrayList<Term> args = new ArrayList<Term>();
    Term a = constantTerm("a", baseType("o"));
    Term b = constantTerm("b", baseType("o"));
    args.add(f);
    args.add(a);
    args.add(b);
    Term result = complete.apply(args);

    // result *should* be: f(f(a,a), b)
    Term faa = new FunctionalTerm(f, a, a);
    Term expected = new FunctionalTerm(f, faa, b);

    assertTrue(result.equals(expected));
  }

  @Test(expected = TypingError.class)
  public void testApplicationTypeFailure() {
    // λx:o -> o -> o.λy:o.x(f(y,y))
    Variable x = new BinderVariable("x", new ArrowType(baseType("o"), arrowType("o", "o")));
    Variable y = createBinder("y", "o");
    Constant f =
      new Constant("f", new ArrowType(baseType("o"), arrowType("o", "o")));
    Term fyy = new FunctionalTerm(f, y, y);
    Term xfyy = new VarTerm(x, fyy);      // note that this has type o -> o
    Term complete = new Abstraction(x, new Abstraction(y, xfyy));

    // expected: type o -> o -> o; putting in something of type o -> o is not okay!
    complete.apply(constantTerm("a", arrowType("o", "o")));
  }

  @Test
  public void testSimpleSubstitution() {  // a substitution where renaming is not an issue
    // build: λx.f(x, g(y)) with g(y) : Bool and f(x, g(c)) : A
    Variable x = createBinder("x", "Int");
    Variable y = new Var("y", baseType("Int"));
    Constant f = new Constant("f", new ArrowType(baseType("Int"), arrowType("Bool", "A")));
    Constant g = new Constant("g", arrowType("Int", "Bool"));
    Term fxgy = new FunctionalTerm(f, x, new FunctionalTerm(g, y));
    Term abs1 = new Abstraction(x, fxgy);

    // build: λx.f(x, g(c))
    Term abs2 = exampleAbstraction(x);

    // make γ = [y:=c]
    Term c = constantTerm("c", baseType("Int"));
    Substitution gamma = new Subst(y, c);

    // and apply it!
    assertTrue(abs1.substitute(gamma).equals(abs2));
  }

  @Test
  public void testRenamingSubstitution() {
    // substitute λx.s with a substitution that maps x to something else
    // TODO
  }

  @Test
  public void testBinderMappedToFree() {
    // substitute λx.s with a substitution that has x in its range
    // TODO
  }

  @Test
  public void testBinderMappedToBound() {
    // substitute λx.s with a substitution that has x occurring bound in some gamma(y)
    // TODO
  }
}

