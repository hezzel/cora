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
 * This class tests whether the functionality that a term is a pattern is correctly implemented in
 * all kinds of terms.
 */
public class TermPatternTest extends TermTestInherit {
  @Test
  public void testPatternWithoutAbstraction() {
    Variable x = new Var("x", new ArrowType(baseType("a"), arrowType("a", "a")));
    Variable y = new BinderVariable("y", baseType("a"));
    Variable z = new BinderVariable("y", baseType("a"));
    Term arg1 = new VarTerm(x, y, z);
    assertTrue(arg1.isPattern());
    Term arg2 = unaryTerm("g", baseType("b"), freeVariable("d", baseType("b")));
    Term fxyzgb = binaryTerm("f", baseType("a"), arg1, arg2);
    assertTrue(fxyzgb.isPattern());
  }

  @Test
  public void testPatternWithAbstraction() {
    Variable x = new Var("x", new ArrowType(baseType("a"), arrowType("a", "a")));
    Variable y = new BinderVariable("y", baseType("a"));
    Variable z = new BinderVariable("y", baseType("a"));
    Term arg1 = new VarTerm(x, y, z);
    Term arg2 = unaryTerm("g", baseType("b"), freeVariable("d", baseType("b")));
    Term fxyzgb = binaryTerm("f", baseType("a"), arg1, arg2);
    Term abs = new Abstraction(z, new Abstraction(y, fxyzgb));
    Term s = unaryTerm("h", baseType("output"), abs);
    assertTrue(s.isPattern());
  }

  @Test
  public void testNonPatternIllegalApplication() {
    Variable x = new Var("x", arrowType("a", "a"));
    Term a = constantTerm("A", baseType("a"));
    Term xa = new VarTerm(x, a);
    Term s = binaryTerm("f", baseType("o"), xa, constantTerm("C", baseType("c")));
    assertFalse(s.isPattern());
  }

  @Test
  public void testAlmostNotAPatternButVariableIsABinder() {
    Variable x = new BinderVariable("x", arrowType("a", "a"));
    Term a = constantTerm("A", baseType("a"));
    Term xa = new VarTerm(x, a);
    Term s = binaryTerm("f", baseType("o"), xa, constantTerm("C", baseType("c")));
    assertTrue(s.isPattern());
  }

  @Test
  public void testNonPatternWithAbstraction() {
    Variable x = new BinderVariable("x", baseType("o"));
    Abstraction abs = new Abstraction(x, x);
    Variable y = new Var("y", new ArrowType(arrowType("o", "o"), baseType("a")));
    Term yabs = new VarTerm(y, abs);
    assertFalse(yabs.isPattern());
  }

  @Test
  public void testNonPatternButEta() {
    Variable x = new BinderVariable("x", baseType("o"));
    Variable z = new BinderVariable("z", arrowType("o", "o"));
    Abstraction abs = new Abstraction(x, new VarTerm(z, x));
    Variable y = new Var("y", new ArrowType(arrowType("o", "o"), baseType("o")));
    Term yabs = new VarTerm(y, abs);
    // yabs = y(λx.z(x)) -- in HRSs this would be considered a pattern because it is eta-equal to
    // y(z) with z a binder variable; in our formalism it is not
    assertFalse(yabs.isPattern());
  }

  @Test
  public void testNonPatternAppliedToFreeVar() {
    Variable x = new Var("x", baseType("o"));
    Variable z = new Var("z", arrowType("o", "o"));
    Term zx = new VarTerm(z, x);
    Term fzx = unaryTerm("f", baseType("a"), zx);
    assertFalse(fzx.isPattern());
  }

  @Test
  public void testNonPatternDuplicateBinderVar() {
    Variable x = new BinderVariable("x", baseType("o"));
    Variable z = new Var("z", new ArrowType(baseType("o"), arrowType("o", "o")));
    Term zxx = new VarTerm(z, x, x);
    Term fzxx = unaryTerm("f", baseType("a"), zxx);
    assertFalse(fzxx.isPattern());
  }

  @Test
  public void testNonLinearPattern() {
    Variable x = new BinderVariable("x", baseType("o"));
    Variable y = new BinderVariable("y", baseType("o"));
    Variable z = new Var("z", new ArrowType(baseType("o"), arrowType("o", "o")));
    Term zxy = new VarTerm(z, x, y);
    Term fzxszxy = binaryTerm("f", baseType("a"), zxy, zxy);
    assertTrue(fzxszxy.isPattern());
  }
}

