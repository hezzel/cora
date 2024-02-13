/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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
import cora.exceptions.IllegalRuleError;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.*;

public class RuleTestFirstOrder {
  private Type baseType(String name) {
    return TypeFactory.createSort(name);
  }

  private Type arrowType(String name1, String name2) {
    return TypeFactory.createArrow(baseType(name1), baseType(name2));
  }

  private FunctionSymbol makeConstant(String name, Type type) {
    return TermFactory.createConstant(name, type);
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = TypeFactory.createArrow(arg.queryType(), output);
    FunctionSymbol f = TermFactory.createConstant(name, arrtype);
    return f.apply(arg);
  }

  @Test
  public void testSuccessfulApplication() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    Variable y = TermFactory.createVar("y", baseType("Bool"));
    Variable z = TermFactory.createVar("z", baseType("Int"));
    FunctionSymbol g = makeConstant("g", arrowType("Int", "Bool"));
    FunctionSymbol f = makeConstant("f",
      TypeFactory.createArrow(baseType("Bool"), arrowType("Bool", "Int")));
    FunctionSymbol h = makeConstant("h",
      TypeFactory.createArrow(baseType("Int"), arrowType("Int", "Int")));
    Term left = TermFactory.createApp(f, g.apply(x), y);
    Term right = TermFactory.createApp(h, x, makeConstant("3", baseType("Int")));
    Rule rule = RuleFactory.createFirstOrderRule(left, right);

    Term instance = TermFactory.createApp(f, TermFactory.createApp(g, TermFactory.createApp(h,
      makeConstant("5", baseType("Int")), z)), makeConstant("true", baseType("Bool")));
    Term target = TermFactory.createApp(h, TermFactory.createApp(h, makeConstant("5", baseType("Int")),
      z), makeConstant("3", baseType("Int")));

    assertTrue(rule.applicable(instance));
    assertTrue(rule.apply(instance).equals(target));
  }

  @Test
  public void testFailedApplication() {
    Variable x = TermFactory.createVar("x", baseType("Int"));
    FunctionSymbol f = makeConstant("f",
      TypeFactory.createArrow(baseType("Int"), arrowType("Int", "Int")));
    Rule rule = RuleFactory.createFirstOrderRule(TermFactory.createApp(f, x, x), x);
    Term noninstance = TermFactory.createApp(f, makeConstant("1", baseType("Int")),
      makeConstant("2", baseType("Int")));

    assertFalse(rule.applicable(noninstance));
    assertTrue(rule.apply(noninstance) == null);
  }
}

