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
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;

/**
 * This class tests equality for all kinds of term.
 * By definition, this is about equality of *equivalence classes*, so alpha-equality.
 */
public class AlphaEqualityTest extends TermTestInherit {
  @Test
  public void testInequalityBetweenBinderVariables() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = binderVariable("x", baseType("o"));
    assertFalse(x.equals(y));
  }

  @Test
  public void testEqualityBetweenAbstractions() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = binderVariable("x", baseType("o"));
    Term absx = new Abstraction(x, x);
    Term absy = new Abstraction(y, y);
    assertTrue(absx.equals(absy));
  }

  @Test
  public void testInequalityDueToRenaming1() {
    // λx.x != λy.x
    Variable x = binderVariable("x", baseType("o"));
    Variable y = binderVariable("x", baseType("o"));
    Term absx = new Abstraction(x, x);
    Term absy = new Abstraction(y, x);
    assertFalse(absx.equals(absy));
  }

  @Test
  public void testInequalityDueToRenaming2() {
    // λx.y != λx.x
    Variable x = binderVariable("x", baseType("o"));
    Variable y = binderVariable("x", baseType("o"));
    Term absx = new Abstraction(x, y);
    Term absy = new Abstraction(y, y);
    assertFalse(absx.equals(absy));
  }

  @Test
  public void testObviousEquality() {
    // create: g(λx.f(a, x), y(b))
    Term a = constantTerm("a", baseType("A"));
    Variable x = binderVariable("x", baseType("X"));
    Term fax = binaryTerm("f", baseType("C"), a, x);
    Term abs = new Abstraction(x, fax);   // λx.f(a,x)
    Variable y = freeVariable("y", arrowType("B", "Y"));
    Term b = constantTerm("b", baseType("B"));
    Term yb = new VarTerm(y, b);
    Term total = binaryTerm("g", baseType("A"), abs, yb);
    
    assertTrue(total.equals(total));
  }

  @Test
  public void testObviousEqualityRecreate() {
    // create: g(λx.f(a,x), y(b))
    Term a = constantTerm("a", baseType("A"));
    Variable x = binderVariable("x", baseType("X"));
    Term fax = binaryTerm("f", baseType("C"), a, x);
    Term abs = new Abstraction(x, fax);
    Variable y = freeVariable("y", arrowType("B", "Y"));
    Term b = constantTerm("b", baseType("B"));
    Term yb = new VarTerm(y, b);
    Term total = binaryTerm("g", baseType("A"), abs, yb);

    // create it again!
    FunctionSymbol f = fax.queryRoot();
    Variable z = binderVariable("z", baseType("X"));
    Term faz = new FunctionalTerm(f, constantTerm("a", baseType("A")), z);
    Term zabs = new Abstraction(z, faz);
    Term ybnew = new VarTerm(y, b);
    Term second = binaryTerm("g", baseType("A"), zabs, ybnew);

    assertTrue(total.equals(second));
  }

  @Test
  public void testAlphaEqualBindersAboveEachOther() {
    // create: λy.g(λx.f(y,x), y(b))
    Variable x = binderVariable("x", arrowType("B", "C"));
    Variable y = binderVariable("y", arrowType("B", "C"));
    Term fyx = binaryTerm("f", baseType("A"), y, x);
    Term abs = new Abstraction(x, fyx);
    Term b = constantTerm("b", baseType("B"));
    Term yb = new VarTerm(y, b);
    Term t1 = binaryTerm("g", baseType("A"), abs, yb);
    Term s1 = new Abstraction(y, t1);

    // create: λx.g(λy.f(x,y), x(b))
    Term fxy = binaryTerm("f", baseType("A"), x, y);
    Term newabs = new Abstraction(y, fxy);
    Term xb = new VarTerm(x, b);
    Term t2 = binaryTerm("g", baseType("A"), newabs, xb);
    Term s2 = new Abstraction(x, t2);

    assertTrue(s1.equals(s2));
  }

  @Test
  public void testInequalityDueToTypeMismatchFunction() {
    Term a = constantTerm("a", baseType("A"));
    Term b = constantTerm("b", baseType("B"));
    Term fab1 = binaryTerm("f", baseType("C"), a, b);
    Term fab2 = binaryTerm("f", baseType("D"), a, b);
    assertFalse(fab1.equals(fab2));
  }

  @Test
  public void testInequalityDueToTypeMismatchAbstraction() {
    Variable x = binderVariable("x", baseType("A"));
    Variable y = binderVariable("y", baseType("B"));
    Term s = new Abstraction(x, x);
    Term t = new Abstraction(y, y);
    assertFalse(s.equals(t));
  }
}

