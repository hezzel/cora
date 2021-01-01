/**************************************************************************************************
 Copyright 2020 Cynthia Kop

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
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;

/** This class tests whether the apply function is correctly implemented in all kinds of terms. */
public class TermApplicationTest extends TermTestInherit {
  /** @return a type a → (b → c) → d → e */
  private Type createLongType() {
    return new ArrowType(baseType("a"), new ArrowType(arrowType("b", "c"), arrowType("d", "e")));
  }

  @Test
  public void testApplyToAllArgumentsOfFunction() {
    Variable x = freeVariable("x", baseType("o"));
    Term fx = unaryTerm("f", createLongType(), x);
    ArrayList<Term> lst = new ArrayList<Term>();
    lst.add(constantTerm("A", baseType("a")));
    lst.add(unaryTerm("g", arrowType("b", "c"), x));
    lst.add(binderVariable("y", baseType("d")));

    Term fxapplied = fx.apply(lst);
    assertTrue(fx.toString().equals("f(x)"));   // original term is unchanged
    assertTrue(fxapplied.queryType().equals(baseType("e")));
    assertTrue(fxapplied.toString().equals("f(x, A, g(x), y)"));
  }

  @Test
  public void testApplyToSomeArgumentsOfConstant() {
    Variable x = freeVariable("x", baseType("o"));
    Term f = constantTerm("f", createLongType());
    ArrayList<Term> lst = new ArrayList<Term>();
    lst.add(constantTerm("A", baseType("a")));
    lst.add(unaryTerm("g", arrowType("b", "c"), x));

    Term fapplied = f.apply(lst);
    assertTrue(f.toString().equals("f"));   // original term is unchanged
    assertTrue(fapplied.queryType().equals(arrowType("d", "e")));
    assertTrue(fapplied.toString().equals("f(A, g(x))"));
  }

  @Test
  public void testApplyToOneArgumentOfVarterm() {
    Variable x = freeVariable("x", baseType("o"));
    Variable z = binderVariable("z", new ArrowType(baseType("o"), createLongType()));
    Term zx = new VarTerm(z, x);
    Term zxapplied = zx.apply(constantTerm("A", baseType("a")));
    assertTrue(zx.toString().equals("z(x)"));   // original term is unchanged
    assertTrue(zxapplied.queryType().equals(new ArrowType(arrowType("b", "c"),
                                                          arrowType("d", "e"))));
    assertTrue(zxapplied.toString().equals("z(x, A)"));
  }

  @Test
  public void testApplyToOneArgumentOfVariable() {
    Variable x = binderVariable("x", createLongType());
    Variable z = freeVariable("z", createLongType());
    Term fxx = binaryTerm("f", baseType("a"), x, x);
    Term zapplied = z.apply(fxx);
    assertTrue(zapplied.equals(new VarTerm(z, fxx)));
  }

  @Test
  public void testApplyToNoArgumentsOfFunction() {
    Variable x = freeVariable("x", baseType("o"));
    Term fx = unaryTerm("f", createLongType(), x);
    ArrayList<Term> lst = new ArrayList<Term>();
    Term fxapplied = fx.apply(lst);
    assertTrue(fx.equals(fxapplied));
  }

  @Test
  public void testApplyToNoArgumentsOfAbstraction() {
    Variable x = binderVariable("x", baseType("o"));
    Abstraction abs = new Abstraction(x, x);
    ArrayList<Term> lst = new ArrayList<Term>();
    Term absapplied = abs.apply(lst);
    assertTrue(abs.equals(absapplied));
  }

  @Test
  public void testApplyListToExtendedAbstraction() {
    // λx:A,y:B->C,z:B.f(x, y(b), y(z))
    Variable x = binderVariable("x", baseType("A"));
    Variable y = binderVariable("y", arrowType("B", "C"));
    Variable z = binderVariable("z", baseType("B"));
    Term b = constantTerm("b", baseType("B"));
    Term fxyb = binaryTerm("f", arrowType("C", "D"), x, new VarTerm(y, b));
    Term main = fxyb.apply(new VarTerm(y, z));
    Term abs = new Abstraction(x, new Abstraction(y, new Abstraction(z, main)));

    Term a = constantTerm("a", baseType("A"));
    Variable u = binderVariable("u", baseType("B"));
    Term lugu = new Abstraction(u, unaryTerm("g", baseType("C"), u));   // λu.g(u)
    ArrayList<Term> lst = new ArrayList<Term>();
    lst.add(a);
    lst.add(lugu);
    Term result = abs.apply(lst);

    assertTrue(result.toString().equals("λz.f(a, g(b), g(z))"));
  }

  @Test
  public void testApplyListToSingleAbstraction() {
    // λx:(A->B)->C->D.x(f(a,b))
    Term a = constantTerm("a", baseType("A"));
    Term b = constantTerm("b", baseType("B"));
    Term c = constantTerm("c",baseType("C"));
    Term fab = binaryTerm("f", arrowType("A", "B"), a, b);
    Variable x = binderVariable("x", new ArrowType(arrowType("A", "B"), arrowType("C", "D")));
    Term term = new Abstraction(x, new VarTerm(x, fab));

    // λy:A->B.g(y)
    Variable y = binderVariable("y", arrowType("A", "B"));
    Term gy = unaryTerm("g", arrowType("C", "D"), y);
    Term abs = new Abstraction(y, gy);

    // term.apply[abs,c] = g(f(a,b), c)
    ArrayList<Term> lst = new ArrayList<Term>();
    lst.add(abs);
    lst.add(c);
    assertTrue(term.apply(abs).toString().equals("g(f(a, b))"));
    assertTrue(term.apply(lst).toString().equals("g(f(a, b), c)"));
  }
}

