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
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;
import cora.interfaces.rewriting.Rule;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.AtrsRule;

public class AtrsRuleTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  private Term constantTerm(String name, Type type) {
    return new UserDefinedSymbol(name, type);
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = new ArrowType(arg.queryType(), output);
    UserDefinedSymbol f = new UserDefinedSymbol(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  @Test(expected = NullInitialisationError.class)
  public void testLeftNullCreation() {
    Rule rule = new AtrsRule(constantTerm("a", baseType("b")), null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testRightNullCreation() {
    Rule rule = new AtrsRule(null, constantTerm("a", baseType("b")));
  }

  @Test(expected = TypingError.class)
  public void testIlltypedRule() {
    Var x = new Var("x", baseType("a"));
    Term left = unaryTerm("id", baseType("b"), x);
    Rule rule = new AtrsRule(left, x);
  }

  @Test
  public void testBasics() {
    Var x = new Var("x", baseType("a"));
    Term left = unaryTerm("id", baseType("a"), x);
    Rule rule = new AtrsRule(left, x);
    assertTrue(rule.queryLeftSide().equals(left));
    assertTrue(rule.queryRightSide().equals(x));
    assertTrue(rule.queryType().equals(baseType("a")));
    assertTrue(rule.toString().equals("id(x) → x"));
  }

  @Test
  public void testSuccessfulRootApplication() {
    Var x = new Var("x", baseType("Int"));
    Var y = new Var("y", baseType("Bool"));
    Var z = new Var("z", baseType("Int"));
    UserDefinedSymbol g = new UserDefinedSymbol("g", arrowType("Int", "Bool"));
    UserDefinedSymbol f =
      new UserDefinedSymbol("f", new ArrowType(baseType("Bool"), arrowType("Bool", "Int")));
    UserDefinedSymbol h =
      new UserDefinedSymbol("h", new ArrowType(baseType("Int"), arrowType("Int", "Int")));
    Term left = new FunctionalTerm(f, new FunctionalTerm(g, x), y);
    Term right = new FunctionalTerm(h, x, constantTerm("3", baseType("Int")));
    Rule rule = new AtrsRule(left, right);
    // rule: f(g(x), y) -> h(x, 3)

    Term instance = new FunctionalTerm(f, new FunctionalTerm(g, new FunctionalTerm(h,
      constantTerm("5", baseType("Int")), z)), constantTerm("true", baseType("Bool")));
    Term target = new FunctionalTerm(h, new FunctionalTerm(h, constantTerm("5", baseType("Int")),
      z), constantTerm("3", baseType("Int")));
    // instance: f(g(h(5, z)), true)
    // target: h(h(5, z), 3)

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).equals(target));
    // does rule reduce instance to target?
  }

  @Test
  public void testFailedRootApplication() {
    Var x = new Var("x", baseType("Int"));
    UserDefinedSymbol f =
      new UserDefinedSymbol("f", new ArrowType(baseType("Int"), arrowType("Int", "Int")));
    Rule rule = new AtrsRule(new FunctionalTerm(f, x, x), x);
    // rule: f(x, x) -> x
    Term noninstance = new FunctionalTerm(f, constantTerm("1", baseType("Int")),
      constantTerm("2", baseType("Int")));
    // noninstance: f(1,2)

    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testSuccessfulHeadApplication() {
    Var x = new Var("x", baseType("Int"));
    Type output = new ArrowType(baseType("Bool"), new ArrowType(baseType("Int"), baseType("a")));
    Type longtype = new ArrowType(baseType("Int"), new ArrowType(baseType("Int"), output));
    UserDefinedSymbol f = new UserDefinedSymbol("f", longtype);
    UserDefinedSymbol g = new UserDefinedSymbol("g", new ArrowType(baseType("Int"), output));

    Term left = new FunctionalTerm(f, x, x);
    Term right = new FunctionalTerm(g, x);
    Rule rule = new AtrsRule(left, right);
    // rule: f(x,x) -> g(x)

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("3", baseType("Int")));
    args.add(constantTerm("3", baseType("Int")));
    args.add(constantTerm("true", baseType("Bool")));
    args.add(constantTerm("7", baseType("Int")));
    Term instance = new FunctionalTerm(f, args);
    // instance: f(3,3,true,7)

    ArrayList targs = new ArrayList<Term>();
    targs.add(constantTerm("3", baseType("Int")));
    targs.add(constantTerm("true", baseType("Bool")));
    targs.add(constantTerm("7", baseType("Int")));
    Term target = new FunctionalTerm(g, targs);
    // target: g(3,true,7)

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).equals(target));
  }

  @Test
  public void testFailedHeadApplication() {
    Type xtype = arrowType("Int", "Int");
    Var x = new Var("x", xtype);
    UserDefinedSymbol f = new UserDefinedSymbol("f", new ArrowType(xtype, xtype));
    UserDefinedSymbol g = new UserDefinedSymbol("g", xtype);
  
    Rule rule = new AtrsRule(new FunctionalTerm(f, x), x);
    // rule: f(x) -> x : Int -> Int
  
    Term noninstance = new FunctionalTerm(g, constantTerm("0", baseType("Int")));
    // noninstance: g 0 : Int
  
    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testWrongTypeApplication() {
    Type xtype = arrowType("Bool", "Int");
    Var x = new Var("x", xtype);
    UserDefinedSymbol f = new UserDefinedSymbol("f", new ArrowType(xtype, xtype));
    UserDefinedSymbol g = new UserDefinedSymbol("g", arrowType("Int", "Int"));
  
    Rule rule = new AtrsRule(new FunctionalTerm(f, x), x);
    // rule: f(x) -> x : Bool -> Int
  
    Term noninstance = new FunctionalTerm(g, constantTerm("0", baseType("Int")));
    // noninstance: g 0 : Int
  
    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }
}

