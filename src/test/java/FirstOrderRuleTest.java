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
import java.util.ArrayList;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.exceptions.IllegalRuleError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;
import cora.interfaces.rewriting.Rule;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.FirstOrderRule;

public class FirstOrderRuleTest {
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
    Constant f = new Constant(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  @Test(expected = NullInitialisationError.class)
  public void testLeftNullCreation() {
    Rule rule = new FirstOrderRule(constantTerm("a", baseType("b")), null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testRightNullCreation() {
    Rule rule = new FirstOrderRule(null, constantTerm("a", baseType("b")));
  }

  @Test(expected = TypingError.class)
  public void testIlltypedRule() {
    Var x = new Var("x", baseType("a"));
    Term left = unaryTerm("id", baseType("b"), x);
    Rule rule = new FirstOrderRule(left, x);
  }

  @Test(expected = IllegalRuleError.class)
  public void testVariableLeft() {
    Var x = new Var("x", baseType("a"));
    Term right = unaryTerm("id", baseType("a"), x);
    Rule rule = new FirstOrderRule(x, right);
  }

  @Test(expected = IllegalRuleError.class)
  public void testNotFirstOrder() {
    Type type = arrowType("a", "b");
    Var x = new Var("x", type);
    Term left = unaryTerm("id", type, x);
    Rule rule = new FirstOrderRule(left, x);
  }

  @Test(expected = IllegalRuleError.class)
  public void testFreshVariableInRhs() {
    Var x = new Var("x", baseType("Bool"));
    Var y = new Var("y", baseType("Int"));
    Var z = new Var("z", baseType("Int"));
    Constant f =
      new Constant("f", new ArrowType(baseType("Bool"), arrowType("Int", "o")));
    Term left = new FunctionalTerm(f, x, y);
    Term right = new FunctionalTerm(f, x, z);
    Rule rule = new FirstOrderRule(left, right);
  }

  @Test
  public void testBasics() {
    Var x = new Var("x", baseType("a"));
    Term left = unaryTerm("id", baseType("a"), x);
    Rule rule = new FirstOrderRule(left, x);
    assertTrue(rule.queryLeftSide().equals(left));
    assertTrue(rule.queryRightSide().equals(x));
    assertTrue(rule.queryType().equals(baseType("a")));
    assertTrue(rule.toString().equals("id(x) → x"));
  }

  @Test
  public void testSuccessfulApplication() {
    Var x = new Var("x", baseType("Int"));
    Var y = new Var("y", baseType("Bool"));
    Var z = new Var("z", baseType("Int"));
    Constant g = new Constant("g", arrowType("Int", "Bool"));
    Constant f =
      new Constant("f", new ArrowType(baseType("Bool"), arrowType("Bool", "Int")));
    Constant h =
      new Constant("h", new ArrowType(baseType("Int"), arrowType("Int", "Int")));
    Term left = new FunctionalTerm(f, new FunctionalTerm(g, x), y);
    Term right = new FunctionalTerm(h, x, constantTerm("3", baseType("Int")));
    Rule rule = new FirstOrderRule(left, right);

    Term instance = new FunctionalTerm(f, new FunctionalTerm(g, new FunctionalTerm(h,
      constantTerm("5", baseType("Int")), z)), constantTerm("true", baseType("Bool")));
    Term target = new FunctionalTerm(h, new FunctionalTerm(h, constantTerm("5", baseType("Int")),
      z), constantTerm("3", baseType("Int")));

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).equals(target));
  }

  @Test
  public void testFailedApplication() {
    Var x = new Var("x", baseType("Int"));
    Constant f =
      new Constant("f", new ArrowType(baseType("Int"), arrowType("Int", "Int")));
    Rule rule = new FirstOrderRule(new FunctionalTerm(f, x, x), x);
    Term noninstance = new FunctionalTerm(f, constantTerm("1", baseType("Int")),
      constantTerm("2", baseType("Int")));

    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }
}

