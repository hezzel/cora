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
 * This class tests whether the functionality to verify that a term is first-order is correctly
 * implemented in all kinds of terms.
 */
public class TermFirstOrderTest extends TermTestInherit {
  @Test
  public void testFirstOrderTrue() {
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), freeVariable("d", baseType("b")));
    Term fcgb = binaryTerm("f", baseType("a"), arg1, arg2);
    assertTrue(fcgb.isFirstOrder());
  }

  @Test
  public void testFirstOrderPartiallyApplied() {
    Term arg1 = constantTerm("c", arrowType("a", "a"));
    Term arg2 = unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")));
    Term fcgb = binaryTerm("f", baseType("a"), arg1, arg2);
    assertFalse(fcgb.isFirstOrder());
  }

  @Test
  public void testFirstOrderVarTerm() {
    Variable x = freeVariable("f", arrowType("a", "b"));
    Term arg = constantTerm("c", baseType("a"));
    Term fc = new VarTerm(x, arg);
    assertFalse(fc.isFirstOrder());
  }

  @Test
  public void testFirstOrderBinder() {
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), binderVariable("d", baseType("b")));
    Term fcgb = binaryTerm("f", baseType("a"), arg1, arg2);
    assertFalse(fcgb.isFirstOrder());
  }

  @Test
  public void testFirstOrderIllegalVariable() {
    Variable x = freeVariable("x", arrowType("a", "b"));
    Term fx = unaryTerm("f", baseType("c"), x);
    assertFalse(fx.isFirstOrder());
  }
}

