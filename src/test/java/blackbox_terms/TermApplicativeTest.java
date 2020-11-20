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
 * This class tests whether the check that a term is applicative is correctly implemented in all
 * kinds of terms.
 */
public class TermApplicativeTest extends TermTestInherit {
  /** This creates a term h(y(f(x, a)), g(z)) if x : A and y, z : (B → C) → (B → C) */
  private Term createTerm(Variable x, Variable y, Variable z) {
    Term a = constantTerm("a", baseType("A"));
    Term fxa = binaryTerm("f", arrowType("B", "C"), x, a);
    Term yfxa = new VarTerm(y, fxa);  // y(f(x, a))
    Term gz = unaryTerm("g", baseType("A"), z);
    return binaryTerm("h", baseType("O"), yfxa, gz);
  }
  
  @Test
  public void testFullyApplicativeTerm() {
    Variable x = freeVariable("x", baseType("A"));
    Variable y = freeVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Term t = createTerm(x, y, y);
    assertTrue(t.isApplicative());
  }

  @Test
  public void testApplicativeTermWithOneFirstOrderBinderVariable() {
    Variable x = binderVariable("x", baseType("A"));
    Variable y = freeVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Term t = createTerm(x, y, y);
    assertFalse(t.isApplicative());
  }

  @Test
  public void testApplicativeTermWithOneHigherOrderBinderVariable() {
    Variable x = freeVariable("x", baseType("A"));
    Variable y = freeVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Variable z = binderVariable("z", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Term t = createTerm(x, y, z);
    assertFalse(t.isApplicative());
  }

  @Test
  public void testApplicativeTermWithOneAppliedBinderVariable() {
    Variable x = freeVariable("x", baseType("A"));
    Variable y = binderVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Variable z = freeVariable("z", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Term t = createTerm(x, y, z);
    assertFalse(t.isApplicative());
  }

  @Test
  public void testAbstractionWhereBinderIsNotUsed() {
    Variable x = binderVariable("x", baseType("o"));
    Term a = constantTerm("a", baseType("o"));
    Abstraction abs = new Abstraction(x, a);
    assertFalse(abs.isApplicative());
  }

  @Test
  public void testLargeTermContainingAbstraction() {
    Variable x = freeVariable("x", baseType("A"));
    Variable y = freeVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Variable z = binderVariable("z", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Term t = new Abstraction(z, createTerm(x, y, z));
    Term s = unaryTerm("p", baseType("A"), t);
    assertFalse(t.isApplicative());
  }
}

