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

/** This class tests the freeVars and boundVars functions. */
public class VarsTest extends TermTestInherit {
  @Test
  public void testVarsOfApplicativeTerm() {
    Variable x = freeVariable("x", baseType("A"));
    Variable y = freeVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Term a = constantTerm("a", baseType("A"));
    Term fxa = binaryTerm("f", arrowType("B", "C"), x, a); 
    Term yfxa = new VarTerm(y, fxa);  // y(f(x, a))
    Term gy = unaryTerm("g", baseType("A"), y); 
    Term s = binaryTerm("h", baseType("O"), yfxa, gy);

    Environment frees = s.freeVars();
    Environment bounds = s.boundVars();

    assertTrue(bounds.size() == 0);
    assertTrue(frees.size() == 2);
    assertTrue(frees.contains(x));
    assertTrue(frees.contains(y));
  }

  @Test
  public void testVarsOfApplicativeTermsWithBinderVariables() {
    Variable x = binderVariable("x", baseType("A"));
    Variable y = binderVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Variable z = freeVariable("z", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Term a = constantTerm("a", baseType("A"));
    Term fxa = binaryTerm("f", arrowType("B", "C"), x, a); 
    Term yfxa = new VarTerm(y, fxa);
    Term gz = unaryTerm("g", baseType("A"), z); 
    Term s = binaryTerm("h", baseType("O"), yfxa, gz);

    Environment frees = s.freeVars();
    Environment bounds = s.boundVars();

    assertTrue(bounds.size() == 0);
    assertTrue(frees.size() == 3);
    assertTrue(frees.contains(x));
    assertTrue(frees.contains(y));
    assertTrue(frees.contains(z));
  }

  @Test
  public void testVarsOfTermWithAbstractions() {
    // create: h(y(f(λx.x, a)), g(λz.u))
    Variable x = binderVariable("x", baseType("A"));
    Variable y = freeVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Variable z = binderVariable("z", baseType("B"));
    Variable u = binderVariable("z", baseType("C"));
    Term a = constantTerm("a", baseType("A"));
    Term xx = new Abstraction(x, x);
    Term fxxa = binaryTerm("f", arrowType("B", "C"), xx, a); 
    Term yfxxa = new VarTerm(y, fxxa);  // y(f(λx.x, a))
    Term zu = new Abstraction(z, u);
    Term gzu = unaryTerm("g", baseType("A"), zu); 
    Term s = binaryTerm("h", baseType("O"), yfxxa, gzu);

    Environment frees = s.freeVars();
    Environment bounds = s.boundVars();

    assertTrue(bounds.size() == 2);
    assertTrue(frees.size() == 2);
    assertTrue(bounds.contains(x));
    assertTrue(bounds.contains(z));
    assertTrue(frees.contains(y));
    assertTrue(frees.contains(u));
  }

  @Test
  public void testVarsOfTermWithDuplicateAbstraction() {
    // create: h(y(f(λx.x, a)), g(λx.x))
    Variable x = binderVariable("x", baseType("A"));
    Variable y = freeVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Term a = constantTerm("a", baseType("A"));
    Term xx = new Abstraction(x, x);
    Term fxxa = binaryTerm("f", arrowType("B", "C"), xx, a); 
    Term yfxxa = new VarTerm(y, fxxa);  // y(f(λx.x, a))
    Term gxx = unaryTerm("g", baseType("A"), xx); 
    Term s = binaryTerm("h", baseType("O"), yfxxa, gxx);

    Environment frees = s.freeVars();
    Environment bounds = s.boundVars();

    assertTrue(bounds.size() == 1);
    assertTrue(frees.size() == 1);
    assertTrue(bounds.contains(x));
    assertTrue(frees.contains(y));
  }

  @Test(expected = cora.exceptions.IllegalTermError.class)
  public void testIllegalConstructionLambdaOverLambda() {
    // you cannot bind a variable in a term that already binds that same variable
    Variable x = binderVariable("x", baseType("a"));
    Term abs = new Abstraction(x, x);
    Term fabs = unaryTerm("f", baseType("a"), abs);
    Term total = new Abstraction(x, fabs);    // this should fail
    assertTrue(false);
  }

  @Test(expected = cora.exceptions.IllegalTermError.class)
  public void testIllegalConstructionBinderBesidesLambda() {
    // you cannot bind a variable in a term that uses that same variable free
    Variable x = binderVariable("x", baseType("a"));
    Term abs = new Abstraction(x, x);
    Term fabsx = binaryTerm("f", baseType("a"), abs, x); // this should fail
    assertTrue(false);
  }
}

