/**************************************************************************************************
 Copyright 2018 Cynthia Kop

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
import cora.core.types.*;
import cora.core.terms.*;
import cora.rewriting.SimpleRule;

public class RuleTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  private Term constantTerm(String name, Type type) {
    return new FunctionalTerm(new UserDefinedSymbol(name, type));
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = new ArrowType(arg.queryType(), output);
    UserDefinedSymbol f = new UserDefinedSymbol(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  @Test(expected = NullInitialisationError.class)
  public void leftNullCreation() {
    Rule rule = new SimpleRule(constantTerm("a", baseType("b")), null);
  }

  @Test(expected = NullInitialisationError.class)
  public void rightNullCreation() {
    Rule rule = new SimpleRule(null, constantTerm("a", baseType("b")));
  }

  @Test(expected = TypingError.class)
  public void mistypedRule() {
    Var x = new Var("x", baseType("a"));
    Term left = unaryTerm("id", baseType("b"), x);
    Rule rule = new SimpleRule(left, x);
  }

  @Test
  public void testBasics() {
    Var x = new Var("x", baseType("a"));
    Term left = unaryTerm("id", baseType("a"), x);
    Rule rule = new SimpleRule(left, x);
    assertTrue(rule.queryLeftSide().equals(left));
    assertTrue(rule.queryRightSide().equals(x));
    assertTrue(rule.queryType().equals(baseType("a")));
    assertTrue(rule.toString().equals("id(x) → x"));
  }
}

