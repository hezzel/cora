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

package cora.reader;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import cora.exceptions.ParseError;
import cora.types.Type;
import cora.parser.lib.ErrorCollector;
import cora.parser.CoraParser;
import cora.types.TypeFactory;
import cora.terms.Term;
import cora.terms.Variable;
import cora.terms.FunctionSymbol;
import cora.terms.TermFactory;

public class TermTyperTest {
  private Type type(String str) {
    return CoraParser.readType(str);
  }

  private SymbolData generateSignature() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("f", type("a → b → c → d")));
    data.addFunctionSymbol(TermFactory.createConstant("aa", type("a")));
    data.addFunctionSymbol(TermFactory.createConstant("bb", type("b")));
    data.addFunctionSymbol(TermFactory.createConstant("cc", type("c")));
    data.addFunctionSymbol(TermFactory.createConstant("h", type("(c → d) → b")));
    return data;
  }

  private Term readTerm(String txt, String expected, boolean constrained, SymbolData data,
                        String message) {
    ErrorCollector collector = new ErrorCollector();
    Type exp = expected == null ? null : type(expected);
    if (data == null) data = generateSignature();
    Term ret = TermTyper.readTerm(txt, constrained, data, exp, collector);
    if (!collector.queryCollectedMessages().equals(message)) {
      System.out.println(collector.queryCollectedMessages());
      System.out.println("ret = " + ret);
      assertTrue(false);
    }   
    return ret;
  }

  @Test
  public void testReadSingleString() {
    Term term = readTerm("\"hello world!\\n\"", null, true, null, "");
    assertTrue(term.queryType().toString().equals("String"));
    assertTrue(term.toString().equals("\"hello world!\\n\""));
  }

  @Test
  public void testStringWithIllegalEscapeInIt() {
    Term t = readTerm("\"a\\xb\"", null, true, null,
      "1:1: Cannot parse string \"a\\xb\": stray escape character at position 3: " +
      "\\x is not an escape sequence.\n");
    assertTrue(t.toString().equals("\"a\\xb\""));
  }

  @Test
  public void testStringWithCorrectType() {
    Term t = readTerm("\"test\"", "String", true, null, "");
    assertTrue(t.queryType().toString().equals("String"));
  }

  @Test
  public void testStringWithIncorrectType() {
    Term t = readTerm(" \"test\"", "string", true, null,
      "1:2: Expected term of type string, but got value \"test\" which has type String.\n");
    assertTrue(t.queryType().toString().equals("string"));
    assertTrue(t.toString().equals("\"test\""));
  }

  @Test
  public void testReadUndeclaredVariableWithoutType() {
    Term t = readTerm("xx_yy", null, false, null,
      "1:1: Undeclared symbol: xx_yy.  Type cannot easily be deduced from context.\n");
    assertTrue(t.isVariable());
    assertFalse(t.queryVariable().isBinderVariable());
    assertTrue(t.queryType().equals(TypeFactory.unitSort));
  }

  @Test
  public void testReadUndeclaredVariableWithType() {
    Term t = readTerm("xx_yy", "a -> b", false, null, "");
    assertTrue(t.isVariable());
    assertFalse(t.queryVariable().isBinderVariable());
    assertTrue(t.queryType().toString().equals("a ⇒ b"));
  }

  @Test
  public void testReadDeclaredVariableWithoutType() {
    SymbolData data = generateSignature();
    Variable x = TermFactory.createVar("x", type("(a -> b) -> b"));
    data.addVariable(x);
    Term t = readTerm("x", null, true, data, "");
    assertTrue(t == x);
  }

  @Test
  public void testReadDeclaredVariableWithCorrectType() {
    SymbolData data = generateSignature();
    Variable x = TermFactory.createVar("x", type("(a -> b) -> b"));
    data.addVariable(x);
    Term t = readTerm("x", "(a -> b) -> b", true, data, "");
    assertTrue(t == x);
  }

  @Test
  public void testReadDeclaredVariableWithIncorrectType() {
    SymbolData data = generateSignature();
    Variable x = TermFactory.createVar("x", type("(a -> b) -> b"));
    data.addVariable(x);
    Term t = readTerm("x", "(a -> b)", true, data,
      "1:1: Expected term of type a ⇒ b, but got variable x which has type (a ⇒ b) ⇒ b.\n");
  }

  @Test
  public void testReadBaseConstantWithoutType() {
    Term t = readTerm("aa", null, true, null, "");
    assertTrue(t.equals(TermFactory.createConstant("aa", type("a"))));
  }

  @Test
  public void testReadBaseConstantWithGoodType() {
    Term t = readTerm("aa", "a", false, null, "");
    assertTrue(t.equals(TermFactory.createConstant("aa", type("a"))));
  }

  @Test
  public void testReadBaseConstantWithBadType() {
    Term t = readTerm("aa", "b", false, null, "1:1: Expected term of type b, " +
      "but got function symbol aa which has type a.\n");
    assertTrue(t.equals(TermFactory.createConstant("aa", type("b"))));
  }

  @Test
  public void testReadHigherOrderConstant() {
    Term t = readTerm("f", null, true, null, "");
    assertTrue(t.equals(TermFactory.createConstant("f", type("a → b → c → d"))));
  }

  @Test
  public void testReadDeclaredMetaVariableUsedAsVariableWithNoExpectedType() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("x", type("a → b"), 1));
    Term t = readTerm("x", null, false, data,
      "1:1: Symbol x was previously used (or declared) as a meta-variable with arity > 0; " +
      "here it is used as a variable.\n");
    assertTrue(t.isVariable());
    assertTrue(t.queryType().equals(type("a → b")));
    assertTrue(t.toString().equals("x"));
  }

  @Test
  public void testReadDeclaredMetaVariableUsedAsVariableWithExpectedType() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("x", type("a → b"), 1));
    Term t = readTerm("x", "b", false, data,
      "1:1: Symbol x was previously used (or declared) as a meta-variable with arity > 0; " +
      "here it is used as a variable.\n");
    assertTrue(t.isVariable());
    assertTrue(t.queryType().equals(type("b")));
    assertTrue(t.toString().equals("x"));
  }

  @Test
  public void testReadEmptyApplicationOfConstantWithType() {
    Term t = readTerm("bb()", "b", true, null, "");
    assertTrue(t.equals(TermFactory.createConstant("bb", type("b"))));
  }

  @Test
  public void testReadEmptyApplicationOfConstantWithoutType() {
    Term t = readTerm("f()", null, false, null, "");
    assertTrue(t.equals(TermFactory.createConstant("f", type("a -> b -> c -> d"))));
  }

  @Test
  public void testReadEmptyApplicationWithIncorrectType() {
    Term t = readTerm("f()", "b", false, null, "1:1: Type error: expected term of " +
      "type b, but got f of type a ⇒ b ⇒ c ⇒ d.\n");
    assertTrue(t.equals(TermFactory.createConstant("f", type("b"))));
  }

  @Test
  public void testReadFullApplication() {
    Term t = readTerm("f(aa,bb,cc)", null, true, null, "");
    assertTrue(t.vars().size() == 0);
    assertTrue(t.toString().equals("f(aa, bb, cc)"));
    assertTrue(t.queryType().toString().equals("d"));
  }

  @Test
  public void testReadIncompleteApplication() {
    Term t = readTerm("f(aa,x)", null, false, null, "");
    assertTrue(t.vars().size() == 1);
    assertTrue(t.toString().equals("f(aa, x)"));
    assertTrue(t.queryType().toString().equals("c ⇒ d"));
  }

  @Test
  public void testReadApplicationWithTooManyArgsNoTypeGiven() {
    Term t = readTerm("h(aa, bb)", null, false, null,
      "1:1: Arity error: h has type (c ⇒ d) ⇒ b, but 2 arguments are given.\n");
    assertTrue(t.vars().size() == 0);
    assertTrue(t.toString().equals("h(aa, bb)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("h", type("a → b → b"))));
  }

  @Test
  public void testReadApplicationWithTooManyArgsOutputTypeGiven() {
    Term t = readTerm("h(aa, bb)", "x", false, null,
      "1:1: Arity error: h has type (c ⇒ d) ⇒ b, but 2 arguments are given.\n");
    assertTrue(t.toString().equals("h(aa, bb)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("h", type("a → b → x"))));
  }

  @Test
  public void testReadApplicationWithIncorrectOutputType() {
    Term t = readTerm("f(aa,x,cc)", "c", true, null,
      "1:1: Type error: expected term of type c, but got f(aa, x, cc) of type d.\n");
    assertTrue(t.toString().equals("f(aa, x, cc)"));
    assertTrue(t.isConstant());
    assertTrue(t.queryType().toString().equals("c"));
  }

  @Test
  public void testReadApplicationWithIncorrectArgumentType() {
    Term t = readTerm("f(x,cc,y)", "d", true, null, "1:5: Expected term of type b, " +
      "but got function symbol cc which has type c.\n");
    assertTrue(t.toString().equals("f(x, cc, y)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("f", type("a → b → c → d"))));
    assertTrue(t.queryType().toString().equals("d"));
    assertTrue(t.vars().size() == 2);
  }

  @Test
  public void testReadApplicationWithIncorrectArgumentAndOutputType() {
    Term t = readTerm("f(aa,cc,bb)", "c", false, null,
      "1:6: Expected term of type b, but got function symbol cc which has type c.\n" +
      "1:9: Expected term of type c, but got function symbol bb which has type b.\n" +
      "1:1: Type error: expected term of type c, but got f(aa, cc, bb) of type d.\n");
    assertTrue(t.toString().equals("f(aa, cc, bb)"));
    assertTrue(t.isConstant());
    assertTrue(t.queryType().toString().equals("c"));
  }

  @Test
  public void testReadApplicationWithInconsistentVariables() {
    Term t = readTerm("f(x, bb, x)", null, false, null, "1:10: Expected term of type c, " +
      "but got variable x which has type a.\n");
    assertTrue(t.toString().equals("f(x, bb, x)"));
    assertTrue(t.vars().size() == 1);
  }

  @Test
  public void testNestedFunctionalTerm() {
    Term t = readTerm("f(x,h(f(x, bb)),cc)", null, true, null, "");
    assertTrue(t.toString().equals("f(x, h(f(x, bb)), cc)"));
    assertTrue(t.queryType().equals(type("d")));
    assertTrue(t.vars().size() == 1);
  }

  @Test
  public void testTermWithValues() {
    SymbolData data = generateSignature();
    data.addFunctionSymbol(TermFactory.createConstant("new", type("Int → Bool → String → a → b")));
    Term t = readTerm("new(3,true,\"test\",aa)", null, true, data, "");
    assertTrue(t.toString().equals("new(3, true, \"test\", aa)"));
    assertTrue(t.queryType().toString().equals("b"));
    assertTrue(t.vars().size() == 0);
  }

  @Test
  public void testReadDeclaredVariableApplication() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("a → b → a")));
    Term t = readTerm("Z( aa,x )", null, false, data, "");
    assertTrue(t.toString().equals("Z(aa, x)"));
    assertTrue(t.queryHead().isVariable());
    assertTrue(data.lookupVariable("x").queryType().equals(type("b")));
  }

  @Test
  public void testReadUndeclaredVariableApplication() {
    Term t = readTerm("Z(aa)", "b", false, null,
      // this is not allowed, even though technically we could derive the type
      "1:1: Undeclared symbol: Z.  Type cannot easily be deduced from context.\n");
    assertTrue(t.toString().equals("Z(aa)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("Z", type("a → b"))));
  }

  @Test
  public void testRepeatedApplication() {
    Term t = readTerm("f(aa)(x,cc)", null, true, null, "");
    assertTrue(t.toString().equals("f(aa, x, cc)"));
  }

  @Test
  public void testValueAtHead() {
    Term t = readTerm("12(aa)", null, true, null, 
      "1:1: Arity error: 12 has type Int, but 1 arguments are given.\n");
    assertTrue(t.toString().equals("12(aa)"));
    assertTrue(t.queryType().toString().equals("Int"));
  }

  @Test
  public void testMissingBracket() {
    Term t = readTerm("f(x,h(f(x, bb),cc)", null, false, null,
      "1:19: Expected a comma or closing bracket ) but got end of input.\n");
  }

  @Test
  public void testReadBasicAbstraction() {
    Term t = readTerm("λx :: a. f(x, bb, y)", null, false, null, "");
    assertTrue(t.toString().equals("λx.f(x, bb, y)"));
    assertTrue(t.vars().size() == 1);
    assertTrue(t.queryType().toString().equals("a ⇒ d"));
  }

  @Test
  public void testReadMultipleAbstractionWithBinderDeclarations() {
    Term t = readTerm("λx :: a, y ::c. f(x, bb, y)", null, false, null, "");
    assertTrue(t.toString().equals("λx.λy.f(x, bb, y)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a ⇒ c ⇒ d"));
  }

  @Test
  public void testReadAbstractionWithoutBinderDeclaration() {
    Term t = readTerm("h(\\x.f(aa,bb,x))", null, true, null, "");
    assertTrue(t.toString().equals("h(λx.f(aa, bb, x))"));
    assertTrue(t.vars().size() == 0);
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenButUnnecessary() {
    Term t = readTerm("\\x::a.f(x,bb, cc)", "a -> d", true, null, "");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a ⇒ d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenAndNecessary() {
    Term t = readTerm("λx.f(x,bb, cc)", "a -> d", true, null, "");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a ⇒ d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenThatDoesNotMatchInput() {
    Term t = readTerm("\\x::a.f(x,bb, cc)", "b -> d", false, null,
      "1:2: Type error: expected subterm of type b ⇒ d, but got abstraction with variable of type a.\n" +
      "1:9: Expected term of type a, but got variable x which has type b.\n");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryAbstractionSubterm().vars().size() == 0);
    assertTrue(t.queryType().toString().equals("b ⇒ d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenThatDoesNotMatchOutput() {
    Term t = readTerm("\\x::a.f(x,bb, cc)", "a -> c", false, null,
      "1:7: Type error: expected term of type c, but got f(x, bb, cc) of type d.\n");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a ⇒ c"));
  }

  @Test
  public void testReadAbstractionWhereTypeCannotFullyBeDerived() {
    Term t = readTerm("\\x :: a, y, z :: c.f(x,y,z)", null, true, null,
      "1:10: Cannot derive type of binder y from context; it should be denoted directly in the "+
        "abstraction.\n");
    assertTrue(t.toString().equals("λx.λy1.λz.f(x, y, z)"));
    assertTrue(t.vars().size() == 1);
    assertTrue(t.queryType().toString().equals("a ⇒ o ⇒ c ⇒ d"));
  }

  @Test
  public void testReadAbstractionTypeOfVariableGivenInTheWrongWay() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("x", type("a")));
    Term t = readTerm("λx.x", null, false, data,
      "1:2: Cannot derive type of binder x from context; it should be denoted directly " +
      "in the abstraction.\n");
    assertTrue(t.toString().equals("λx1.x"));
    assertTrue(t.queryType().toString().equals("o ⇒ a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsBinder() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("x", type("a")));
    Term t = readTerm("λx::b.x", null, false, data, "");
    assertTrue(t.toString().equals("λx.x"));
    assertTrue(t.queryType().toString().equals("b ⇒ b"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsFree() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("x", type("a")));
    Term t = readTerm("λx::b.x", null, false, data, "");
    assertTrue(t.toString().equals("λx.x"));
    assertTrue(t.queryType().toString().equals("b ⇒ b"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsFunction() {
    Term t = readTerm("λaa::b.aa", null, true, null,
      "1:2: Ambiguous binder: this name has already been declared as a function symbol.\n");
    assertTrue(t.toString().equals("λaa.aa"));
    assertTrue(t.queryType().toString().equals("b ⇒ a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsMetavariable() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("x", type("a -> b"), 1));
    Term t = readTerm("λx::a.x[ x ]", null, true, data,
      "1:2: Ambiguous binder: this name has already been declared as a meta-variable.\n");
    assertTrue(t.toString().equals("λx1.x⟨x1⟩"));
    assertTrue(t.queryType().toString().equals("a ⇒ b"));
    assertTrue(data.lookupMetaVariable("x").queryType().toString().equals("a ⇒ b"));
  }

  @Test
  public void testReadAbstractionWithDuplicateVariableName() {
    SymbolData data = generateSignature();
    Term t = readTerm("λx::a, y :: b, x :: c.x", null, false, data, "");
    assertTrue(t.toString().equals("λx.λy.λx1.x1"));
    assertTrue(t.queryType().toString().equals("a ⇒ b ⇒ c ⇒ c"));
    assertTrue(data.lookupVariable("x") == null);
  }

  @Test
  public void testReadAbstractionAtHeadOfApplication() {
    Term t = readTerm("(λx :: a, y ::c. f(x,bb,y))(aa,cc)", null, false, null, "");
    assertTrue(t.toString().equals("(λx.λy.f(x, bb, y))(aa, cc)"));
    assertTrue(t.queryType().toString().equals("d"));
  }

  @Test
  public void testReadAbstractionWithMissingType() {
    ErrorCollector collector = new ErrorCollector(10);
    Term t = readTerm("λx :: .x y", "o → o", false, null,
      "1:7: Expected a type (started by a sort identifier or bracket) but got DOT (.).\n" +
      "1:10: Expected end of input but got IDENTIFIER (y).\n");
    assertTrue(t == null);
  }

  @Test
  public void testReadMultipleAbstractionWithMissingComma() {
    Term t = readTerm("\\x :: a y.f(x,y,cc)", "a -> b -> d", false, null,
      "1:9: Expected a comma or dot but got IDENTIFIER (y).\n");
    assertTrue(t.toString().equals("λx.λy.f(x, y, cc)"));
    assertTrue(t.queryType().toString().equals("a ⇒ b ⇒ d"));
  }
}

