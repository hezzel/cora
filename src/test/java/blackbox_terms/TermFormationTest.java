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
 * This class tests the constructions for all kinds of terms, and whether the basic toString()
 * functionality does what you would expect.
 */
public class TermFormationTest extends TermTestInherit {
  @Test
  public void testVariableToString() {
    Term x = binderVariable("xx", baseType("o"));
    Term y = freeVariable("x", arrowType("a", "x"));
    assertTrue(x.toString().equals("xx"));
    assertTrue(y.toString().equals("x"));
  }

  @Test
  public void testConstantToString() {
    Term a = constantTerm("a", arrowType("a", "x"));
    assertTrue(a.toString().equals("a"));
  }

  @Test
  public void testFunctionalTermToString() {
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")));
    Term fcgb = binaryTerm("f", baseType("a"), arg1, arg2);
    assertTrue(fcgb.toString().equals("f(c, g(d))"));
  }

  @Test
  public void testVarTermToString() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    Variable x = freeVariable("f", type);
    Variable y = binderVariable("g", arrowType("b", "b"));
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = new VarTerm(y, constantTerm("d", baseType("b")));
    Term fcgb = new VarTerm(x, arg1, arg2);
    assertTrue(fcgb.toString().equals("f(c, g(d))"));
  }

  @Test
  public void testEasyAbstractionToString() {
    Variable x = binderVariable("x", baseType("a"));
    Variable y = freeVariable("y", baseType("b"));
    Term s = binaryTerm("f", baseType("c"), x, y);
    Term abs = new Abstraction(x, s);
    assertTrue(abs.toString().equals("λx.f(x, y)"));
  }

  @Test
  public void testIckyAbstractionToString() {
    Variable x = binderVariable("x", baseType("a"));
    Variable y = freeVariable("x", baseType("b"));
    Term s = binaryTerm("f", baseType("c"), x, y);
    Term abs = new Abstraction(x, s);
    assertTrue(abs.toString().equals("λx.f(x, x)"));
  }
}

