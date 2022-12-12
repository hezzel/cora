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

package cora.rewriting;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.*;

public class AtrsRuleTest {
  private Type baseType(String name) {
    return TypeFactory.createSort(name);
  }

  private Type arrowType(String name1, String name2) {
    return TypeFactory.createArrow(baseType(name1), baseType(name2));
  }

  private Type arrowType(Type inp, Type outp) {
    return TypeFactory.createArrow(inp, outp);
  }

  private FunctionSymbol makeConstant(String name, Type type) {
    return TermFactory.createConstant(name, type);
  }

  private Term makeApp(FunctionSymbol head, Term arg1, Term arg2) {
    return TermFactory.createApp(head, arg1, arg2);
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = arrowType(arg.queryType(), output);
    FunctionSymbol f = makeConstant(name, arrtype);
    return f.apply(arg);
  }

  @Test(expected = NullInitialisationError.class)
  public void testLeftNullCreation() {
    Rule rule = new AtrsRule(makeConstant("a", baseType("b")), null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testRightNullCreation() {
    Rule rule = new AtrsRule(null, makeConstant("a", baseType("b")));
  }

  @Test(expected = TypingError.class)
  public void testIlltypedRule() {
    Variable x = TermFactory.createVar("x", baseType("a"));
    Term left = unaryTerm("id", baseType("b"), x);
    Rule rule = new AtrsRule(left, x);
  }

  @Test
  public void testBasics() {
    Variable x = TermFactory.createVar("x", baseType("a"));
    Term left = unaryTerm("id", baseType("a"), x);
    Rule rule = new AtrsRule(left, x);
    assertTrue(rule.queryLeftSide().equals(left));
    assertTrue(rule.queryRightSide().equals(x));
    assertTrue(rule.queryType().equals(baseType("a")));
    assertTrue(rule.toString().equals("id(x) → x"));
  }

  @Test
  public void testSuccessfulRootApplication() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Variable y = TermFactory.createVar("y", baseType("Bool"));
    Variable z = TermFactory.createVar("z", baseType("Int"));
    FunctionSymbol g = makeConstant("g", arrowType("Int", "Bool"));
    FunctionSymbol f = makeConstant("f", arrowType(baseType("Bool"), arrowType("Bool", "Int")));
    FunctionSymbol h = makeConstant("h", arrowType(baseType("Int"), arrowType("Int", "Int")));
    Term left = makeApp(f, g.apply(x), y);
    Term right = makeApp(h, x, makeConstant("3", baseType("Int")));
    Rule rule = new AtrsRule(left, right);
    // rule: f(g(x), y) -> h(x, 3)

    Term instance = makeApp(f, g.apply(makeApp(h, makeConstant("5", baseType("Int")), z)),
      makeConstant("true", baseType("Bool")));
    Term target = makeApp(h, makeApp(h, makeConstant("5", baseType("Int")), z),
      makeConstant("3", baseType("Int")));
    // instance: f(g(h(5, z)), true)
    // target: h(h(5, z), 3)

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).equals(target));
    // does rule reduce instance to target?
  }

  @Test
  public void testFailedRootApplication() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    FunctionSymbol f =
      makeConstant("f", arrowType(baseType("Int"), arrowType("Int", "Int")));
    Rule rule = new AtrsRule(makeApp(f, x, x), x);
    // rule: f(x, x) -> x
    Term noninstance = makeApp(f, makeConstant("1", baseType("Int")),
      makeConstant("2", baseType("Int")));
    // noninstance: f(1,2)

    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testSuccessfulHeadApplication() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Type output = arrowType(baseType("Bool"),
      arrowType(baseType("Int"), baseType("a")));
    Type longtype = arrowType(baseType("Int"),
      arrowType(baseType("Int"), output));
    FunctionSymbol f = makeConstant("f", longtype);
    FunctionSymbol g = makeConstant("g", arrowType(baseType("Int"), output));

    Term left = makeApp(f, x, x);
    Term right = g.apply(x);
    Rule rule = new AtrsRule(left, right);
    // rule: f(x,x) -> g(x)

    ArrayList<Term> args = new ArrayList<Term>();
    args.add(makeConstant("3", baseType("Int")));
    args.add(makeConstant("3", baseType("Int")));
    args.add(makeConstant("true", baseType("Bool")));
    args.add(makeConstant("7", baseType("Int")));
    Term instance = f.apply(args);
    // instance: f(3,3,true,7)

    ArrayList<Term> targs = new ArrayList<Term>();
    targs.add(makeConstant("3", baseType("Int")));
    targs.add(makeConstant("true", baseType("Bool")));
    targs.add(makeConstant("7", baseType("Int")));
    Term target = g.apply(targs);
    // target: g(3,true,7)

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).equals(target));
  }

  @Test
  public void testFailedHeadApplication() {
    Type xtype = arrowType("Int", "Int");
    Variable x = TermFactory.createVar("x", xtype);
    FunctionSymbol f = makeConstant("f", arrowType(xtype, xtype));
    FunctionSymbol g = makeConstant("g", xtype);
  
    Rule rule = new AtrsRule(f.apply(x), x);
    // rule: f(x) -> x : Int -> Int
  
    Term noninstance = g.apply(makeConstant("0", baseType("Int")));
    // noninstance: g 0 : Int
  
    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }

  @Test
  public void testWrongTypeApplication() {
    Type xtype = arrowType("Bool", "Int");
    Variable x = TermFactory.createVar("x", xtype);
    FunctionSymbol f = makeConstant("f", arrowType(xtype, xtype));
    FunctionSymbol g = makeConstant("g", arrowType("Int", "Int"));
  
    Rule rule = new AtrsRule(f.apply(x), x);
    // rule: f(x) -> x : Bool -> Int
  
    Term noninstance = g.apply(makeConstant("0", baseType("Int")));
    // noninstance: g 0 : Int
  
    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }
}

