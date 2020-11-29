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
import java.util.List;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;
import cora.terms.positions.*;

/** This class tests the functions relating to Positions in terms. */
public class PositionsTest extends TermTestInherit {
  /** @return a term create: h(y(f(λx.x, a)), g(λz.p(u))) */
  private Term createTestTerm() {
    Variable x = binderVariable("x", baseType("A"));
    Variable y = freeVariable("y", new ArrowType(arrowType("B", "C"), arrowType("C", "B")));
    Variable z = binderVariable("z", baseType("B"));
    Variable u = binderVariable("u", baseType("C"));
    Term a = constantTerm("a", baseType("A"));
    Term xx = new Abstraction(x, x);
    Term fxxa = binaryTerm("f", arrowType("B", "C"), xx, a); 
    Term yfxxa = new VarTerm(y, fxxa);  // y(f(λx.x, a))
    Term zpu = new Abstraction(z, unaryTerm("p", baseType("C"), u));
    Term gzpu = unaryTerm("g", baseType("A"), zpu); 
    return binaryTerm("h", baseType("O"), yfxxa, gzpu);
  }

  /** A shortcut to quickly create argument positions for functional terms */
  private Position farg(int i, Position p) {
    return SubPosition.makeFunctionalPos(i, p);
  }

  /** A shortcut to quickly create argument positions for varterms */
  private Position varg(int i, Position p) {
    return SubPosition.makeVartermPos(i, p);
  }

  /** A shortcut to quickly create abstraction positions */
  private Position abs(Position p) {
    return SubPosition.makeAbstractionPos(p);
  }

  /** A shortcut to quickly create the empty position */
  private Position empty() {
    return new RootPosition();
  }

  @Test
  public void testPositions() {
    Term s = createTestTerm();
    List<Position> posses = s.queryAllPositions();
    assertTrue(posses.get(0).equals(farg(1, varg(1, farg(1, abs(empty()))))));
    assertTrue(posses.get(1).equals(farg(1, varg(1, farg(1, empty())))));
    assertTrue(posses.get(2).equals(farg(1, varg(1, farg(2, empty())))));
    assertTrue(posses.get(3).equals(farg(1, varg(1, empty()))));
    assertTrue(posses.get(4).equals(farg(1, empty())));
    assertTrue(posses.get(5).equals(farg(2, farg(1, abs(farg(1, empty()))))));
    assertTrue(posses.get(6).equals(farg(2, farg(1, abs(empty())))));
    assertTrue(posses.get(7).equals(farg(2, farg(1, empty()))));
    assertTrue(posses.get(8).equals(farg(2, empty())));
    assertTrue(posses.get(9).equals(empty()));
    assertTrue(posses.size() == 10);
  }

  @Test
  public void testSubtermAtPosition() {
    Term s = createTestTerm();
    Variable x = binderVariable("x", baseType("A"));
    assertTrue(s.querySubterm(farg(1, varg(1, farg(1, empty())))).equals(new Abstraction(x, x)));
    assertTrue(s.querySubterm(empty()).equals(s));
    assertTrue(s.querySubterm(farg(2, farg(1, abs(empty())))).toString().equals("p(u)"));
  }

  @Test
  public void testCorrectSubtermReplacement() {
    Term s = createTestTerm();

    // replace λx.x by λz.z (of the same type)
    Variable z = binderVariable("z", baseType("A"));
    Term abs = new Abstraction(z, z);
    Term t1 = s.replaceSubterm(farg(1, varg(1, farg(1, empty()))), abs);
    assertTrue(s.equals(t1));

    // replace g(λz.p(u)) by b(z) for b a fresh constant
    Term bz = unaryTerm("b", baseType("A"), z);
    Term t2 = s.replaceSubterm(farg(2, empty()), bz);
    assertFalse(s.equals(t2));
    assertTrue(t2.toString().equals("h(y(f(λx.x, a)), b(z))"));
  }

  @Test
  public void testCorrectSubtermReplacementBelowAbstraction() {
    Term s = createTestTerm();
    Variable x = s.querySubterm(farg(1, varg(1, farg(1, abs(empty()))))).queryVariable();
    Variable newx = binderVariable("x", baseType("A"));
    Term bx = unaryTerm("b", baseType("A"), x);

    // replace x by itself
    Term t1 = s.replaceSubterm(farg(1, varg(1, farg(1, abs(empty())))), x);
    // replace x by a different variable also called x; this makes it unbound
    Term t2 = s.replaceSubterm(farg(1, varg(1, farg(1, abs(empty())))), newx);
    // replace x by b(x)
    Term t3 = s.replaceSubterm(farg(1, varg(1, farg(1, abs(empty())))), bx);

    // replacing a bound variable by itself does not change anything: the term does not become free
    assertTrue(t1.equals(s));
    assertFalse(t1.freeVars().contains(x.queryVariable()));

    // replacing a bound variable by a different variable frees it, however
    assertFalse(t2.equals(s));
    assertTrue(t2.freeVars().contains(newx));
    
    // nevertheless, t1 and t2 look the same
    assertTrue(t1.toString().equals(t2.toString()));

    // also in t3, the variable did not become free
    assertFalse(t3.freeVars().contains(x));
    assertTrue(t3.toString().equals("h(y(f(λx.b(x), a)), g(λz.p(u)))"));
  }

  @Test(expected = cora.exceptions.IndexingError.class)
  public void testSubtermAtIllegalArgumentPositionBelowFunction() {
    Term s = createTestTerm();
    s.querySubterm(farg(2, farg(2, empty())));
  }

  @Test(expected = cora.exceptions.IndexingError.class)
  public void testSubtermAtIllegalVartermPositionBelowFunction() {
    Term s = createTestTerm();
    s.querySubterm(varg(1, varg(1, empty())));
  }

  @Test(expected = cora.exceptions.IndexingError.class)
  public void testSubtermAtIllegalAbstractionPositionBelowVariable() {
    Term s = createTestTerm();
    Term t = s.querySubterm(farg(1, abs(empty())));
  }
  
  @Test(expected = cora.exceptions.IndexingError.class)
  public void testSubtermAtIllegalFunctionPositionBelowAbstraction() {
    Term s = createTestTerm();
    s.querySubterm(farg(2, farg(1, farg(1, empty()))));
  }

  @Test(expected = cora.exceptions.TypingError.class)
  public void testSubtermReplacementIllegalType() {
    Term s = createTestTerm();

    // replace λx.x by λz.z (of the same type)
    Variable z = binderVariable("z", baseType("a"));
    Term abs = new Abstraction(z, z);
    s.replaceSubterm(farg(1, varg(1, farg(1, empty()))), abs);
  }

  @Test(expected = cora.exceptions.IndexingError.class)
  public void testSubtermReplacementIllegalPosition() {
    Term s = createTestTerm();

    s.replaceSubterm(farg(1, varg(1, farg(3, empty()))), constantTerm("b", baseType("B")));
  }
}

