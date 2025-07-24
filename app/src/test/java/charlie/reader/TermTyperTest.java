/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.reader;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.CoraParser;
import charlie.terms.*;

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
    if (!collector.toString().equals(message)) {
      System.out.println(collector.toString());
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
    assertTrue(t.queryType().equals(TypeFactory.defaultSort));
  }

  @Test
  public void testReadUndeclaredVariableWithType() {
    Term t = readTerm("xx_yy", "a -> b", false, null, "");
    assertTrue(t.isVariable());
    assertFalse(t.queryVariable().isBinderVariable());
    assertTrue(t.queryType().toString().equals("a → b"));
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
      "1:1: Expected term of type a → b, but got variable x which has type (a → b) → b.\n");
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
      "type b, but got f of type a → b → c → d.\n");
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
    assertTrue(t.queryType().toString().equals("c → d"));
  }

  @Test
  public void testReadApplicationWithTooManyArgsNoTypeGiven() {
    Term t = readTerm("h(aa, bb)", null, false, null,
      "1:1: Arity error: h has type (c → d) → b, but 2 arguments are given.\n");
    assertTrue(t.vars().size() == 0);
    assertTrue(t.toString().equals("h(aa, bb)"));
    assertTrue(t.queryHead().equals(TermFactory.createConstant("h", type("a → b → b"))));
  }

  @Test
  public void testReadApplicationWithTooManyArgsOutputTypeGiven() {
    Term t = readTerm("h(aa, bb)", "x", false, null,
      "1:1: Arity error: h has type (c → d) → b, but 2 arguments are given.\n");
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
    assertTrue(t.queryType().toString().equals("a → d"));
  }

  @Test
  public void testReadMultipleAbstractionWithBinderDeclarations() {
    Term t = readTerm("λx :: a, y ::c. f(x, bb, y)", null, false, null, "");
    assertTrue(t.toString().equals("λx.λy.f(x, bb, y)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a → c → d"));
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
    assertTrue(t.queryType().toString().equals("a → d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenAndNecessary() {
    Term t = readTerm("λx.f(x,bb, cc)", "a -> d", true, null, "");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a → d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenThatDoesNotMatchInput() {
    Term t = readTerm("\\x::a.f(x,bb, cc)", "b -> d", false, null,
      "1:2: Type error: expected subterm of type b → d, but got abstraction with variable of type a.\n" +
      "1:9: Expected term of type a, but got variable x which has type b.\n");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryAbstractionSubterm().vars().size() == 0);
    assertTrue(t.queryType().toString().equals("b → d"));
  }

  @Test
  public void testReadAbstractionWithTypeExpectationGivenThatDoesNotMatchOutput() {
    Term t = readTerm("\\x::a.f(x,bb, cc)", "a -> c", false, null,
      "1:7: Type error: expected term of type c, but got f(x, bb, cc) of type d.\n");
    assertTrue(t.toString().equals("λx.f(x, bb, cc)"));
    assertTrue(t.vars().size() == 0);
    assertTrue(t.queryType().toString().equals("a → c"));
  }

  @Test
  public void testReadAbstractionWhereTypeCannotFullyBeDerived() {
    Term t = readTerm("\\x :: a, y, z :: c.f(x,y,z)", null, true, null,
      "1:10: Cannot derive type of binder y from context; it should be denoted directly in the "+
        "abstraction.\n");
    assertTrue(t.toString().equals("λx.λy1.λz.f(x, y, z)"));
    assertTrue(t.vars().size() == 1);
    assertTrue(t.queryType().toString().equals("a → o → c → d"));
  }

  @Test
  public void testAbstractionWithNonArrowTypeExpected() {
    Term t = readTerm("λx::a.x", "(|b,b|)", false, null,
      "1:2: Type error: expected subterm of type ⦇ b, b ⦈, but got abstraction, which " +
      "necessarily has an arrow type.\n");
    assertTrue(t.toString().equals("abs(λx.x)"));
    assertFalse(t.isAbstraction());
  }

  @Test
  public void testReadAbstractionTypeOfVariableGivenInTheWrongWay() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("x", type("a")));
    Term t = readTerm("λx.x", null, false, data,
      "1:2: Cannot derive type of binder x from context; it should be denoted directly " +
      "in the abstraction.\n");
    assertTrue(t.toString().equals("λx1.x"));
    assertTrue(t.queryType().toString().equals("o → a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsBinder() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("x", type("a")));
    Term t = readTerm("λx::b.x", null, false, data, "");
    assertTrue(t.toString().equals("λx.x"));
    assertTrue(t.queryType().toString().equals("b → b"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsFree() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("x", type("a")));
    Term t = readTerm("λx::b.x", null, false, data, "");
    assertTrue(t.toString().equals("λx.x"));
    assertTrue(t.queryType().toString().equals("b → b"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsFunction() {
    Term t = readTerm("λaa::b.aa", null, true, null,
      "1:2: Ambiguous binder: this name has already been declared as a function symbol.\n");
    assertTrue(t.toString().equals("λaa.aa"));
    assertTrue(t.queryType().toString().equals("b → a"));
  }

  @Test
  public void testReadAbstractionWhenParseDataAlreadyContainsVariableAsMetavariable() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("x", type("a -> b"), 1));
    Term t = readTerm("λx::a.x[ x ]", null, true, data,
      "1:2: Ambiguous binder: this name has already been declared as a meta-variable.\n");
    assertTrue(t.toString().equals("λx1.x⟨x1⟩"));
    assertTrue(t.queryType().toString().equals("a → b"));
    assertTrue(data.lookupMetaVariable("x").queryType().toString().equals("a → b"));
  }

  @Test
  public void testReadAbstractionWithDuplicateVariableName() {
    SymbolData data = generateSignature();
    Term t = readTerm("λx::a, y :: b, x :: c.x", null, false, data, "");
    assertTrue(t.toString().equals("λx.λy.λx1.x1"));
    assertTrue(t.queryType().toString().equals("a → b → c → c"));
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
    Term t = readTerm("λx :: .x y", "o → o", false, null,
      "1:7: Expected a type (started by a sort identifier or bracket) but got DOT (.).\n" +
      "1:10: Expected end of input but got IDENTIFIER (y).\n");
    assertTrue(t == null);
  }

  @Test
  public void testGoodTupleWithoutType() {
    Term t = readTerm("(| aa, f(x), 4 |)", null, true, null, "");
    assertTrue(t.isTuple());
    assertTrue(t.queryType().toString().equals("⦇ a, b → c → d, Int ⦈"));
    assertTrue(t.toString().equals("⦇aa, f(x), 4⦈"));
  }

  @Test
  public void testGoodTupleWithCorrectType() {
    Term t = readTerm("⦇ x, true, 4 |)", "⦇ a → b, Bool, Int ⦈", true, null, "");
    assertTrue(t.isTuple());
  }

  @Test
  public void testTupleWithIncorrectType() {
    Term t = readTerm("⦇ aa, true ⦈", "⦇ a → b, Bool ⦈", true, null,
      "1:3: Expected term of type a → b, but got function symbol aa which has type a.\n");
    assertTrue(t.isTuple());
  }

  @Test
  public void testTupleWithIncorrectLength() {
    Term t = readTerm("⦇ aa, true ⦈", "⦇ (a → b), Bool, Int ⦈", true, null,
      "1:1: Type error: expected a term of type ⦇ a → b, Bool, Int ⦈ but got a tuple " +
      "of length 2.\n");
    assertFalse(t.isTuple());
    assertTrue(t.toString().equals("⦇aa, true⦈"));
    assertTrue(t.queryType().toString().equals("⦇ a → b, Bool, Int ⦈"));
  }

  @Test
  public void testTupleWithNonTupleType() {
    Term t = readTerm("⦇ aa, true ⦈", "a → b", false, null,
      "1:1: Type error: expected a term of type a → b but got a tuple, which necessarily has " +
      "a product type.\n");
    assertFalse(t.isTuple());
    assertTrue(t.toString().equals("⦇aa, true⦈"));
    assertTrue(t.queryType().toString().equals("a → b"));
  }

  @Test
  public void testTooShortTuples() {
    Term t = readTerm("(| |)", null, false, null, "1:1: Empty tuples are not allowed.\n");
    assertTrue(t == null);
    t = readTerm("(| 12 |)", null, true, null, "1:1: Tuples of length 1 are not allowed.\n");
    assertTrue(t.isValue());
    assertTrue(t.toValue().getInt() == 12);
  }

  @Test
  public void testReadMultipleAbstractionWithMissingComma() {
    Term t = readTerm("\\x :: a y.f(x,y,cc)", "a -> b -> d", false, null,
      "1:9: Expected a comma or dot but got IDENTIFIER (y).\n");
    assertTrue(t.toString().equals("λx.λy.f(x, y, cc)"));
    assertTrue(t.queryType().toString().equals("a → b → d"));
  }

  @Test
  public void testUndeclaredMetaVariableWithEmptyArgumentsListTypeGiven() {
    Term t = readTerm("Z[]", "a → b", false, null, "");
    assertTrue(t.isVariable());
    assertTrue(t.queryType().equals(type("a → b")));
    assertTrue(t.toString().equals("Z"));
  }

  @Test
  public void testUndeclaredMetaVariableWithEmptyArgumentsListTypeNotGiven() {
    Term t = readTerm("Z⟨⟩", null, true, null,
      "1:1: Undeclared (meta-)variable: Z.  Type cannot easily be deduced from context.\n");
    assertTrue(t.isVariable());
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(t.toString().equals("Z"));
  }

  @Test
  public void testDeclaredMetaVariableWithEmptyArgumentsListCorrectTypeGiven() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("b")));
    Term t = readTerm("Z[⟩", "b", false, data, "");
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("b")));
  }

  @Test
  public void testDeclaredMetaVariableWithEmptyArgumentsListIncorrectTypeGiven() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("b → a")));
    Term t = readTerm("Z⟨⟩", "a → b", true, data, "1:1: Expected term of type a → b, " +
      "but got Z, which was previously used as a variable of type b → a.\n");
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("a → b")));
    assertTrue(data.lookupVariable("Z").queryType().equals(type("b → a")));
  }

  @Test
  public void testDeclaredMetaVariableWithEmptyArgumentsListTypeNotGiven() {
    SymbolData data = generateSignature();
    // declared as higher type
    data.addVariable(TermFactory.createVar("Z", type("b → a")));
    Term t = readTerm("Z⟨]", null, true, data, "");
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("b → a")));
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsListDeclaredAsFunctionSymbol() {
    Term t = readTerm("aa[]", null, false, null, "1:1: Meta-application for meta-variable aa, " +
      "which was previously declared as a function symbol.\n");
    assertTrue(t.toString().equals("aa"));
    assertTrue(t.isVariable());
    assertTrue(t.queryType().toString().equals("a"));
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsListDeclaredAsBinder() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("Z", type("b → a")));
    Term t = readTerm("Z[]", "x", true, data, "1:1: Binder variable Z used as meta-variable.\n");
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("x")));
  }

  @Test
  public void testMetaVariableWithEmptyArgumentsListDeclaredAsHigherMetaVar() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("b → a"), 1));
    Term t = readTerm("Z⟨⟩", null, false, data,
      "1:1: Meta-application for meta-variable Z has no arguments, when it previously occurred " +
      "(or was declared) with arity 1.\n");
    assertTrue(t.isVariable());
    assertTrue(t.toString().equals("Z"));
    assertTrue(t.queryType().equals(type("b → a")));
  }

  @Test
  public void testMetaApplicationWithUndeclaredMetaButDeclaredArgsTypeKnown() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("x", type("a")));
    Term t = readTerm("Z⟨x⟩", "b -> c", false, data, "");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("b → c"));
    MetaVariable z = data.lookupMetaVariable("Z");
    assertTrue(z.queryArity() == 1);
    assertTrue(z.queryType().toString().equals("a → b → c"));
  }

  @Test
  public void testMetaApplicationWithUndeclaredMetaButDeclaredArgsTypeUnknown() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createBinder("x", type("a")));
    Term t = readTerm("Z[x]", null, false, data,
      "1:1: Cannot derive output type of meta-variable Z from context.\n");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(data.lookupMetaVariable("Z") == null);
  }

  @Test
  public void testMetaApplicationWithDeclaredMetaButUndeclaredArg() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a"), 1));
    Term t = readTerm("Z[x]", null, true, data, "");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("a"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
  }

  @Test
  public void testMetaApplicationWithEverythingDeclaredButIncorrectType() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a"), 1));
    Term t = readTerm("Z[x⟩", "b", true, data,
      "1:1: Meta-variable Z has output type a while a term of type b was expected.\n");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("b"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
  }

  @Test
  public void testMetaApplicationWithNothingDeclared() {
    Term t = readTerm("Z[x,aa,y]", null, false, null,
      "1:1: Cannot derive output type of meta-variable Z from context.\n" +
      "1:3: Undeclared symbol: x.  Type cannot easily be deduced from context.\n" +
      "1:8: Undeclared symbol: y.  Type cannot easily be deduced from context.\n");
    assertTrue(t.toString().equals("Z⟨x, aa, y⟩"));
    assertTrue(t.queryType().toString().equals("o"));
  }

  @Test
  public void testMetaApplicationWithJustOnePartMissing() {
    Term t = readTerm("Z[x,aa]", "u", true, null,
      "1:3: Undeclared symbol: x.  Type cannot easily be deduced from context.\n");
    assertTrue(t.toString().equals("Z⟨x, aa⟩"));
    assertTrue(t.queryType().toString().equals("u"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsFunctionSymbolWithTypeExpected() {
    Term t = readTerm("f⟨aa,y]", "c → e", true, null,
      "1:1: Unexpected meta-application with meta-variable f, which was previously declared " +
        "as a function symbol.\n" +
      "1:6: Undeclared symbol: y.  Type cannot easily be deduced from context.\n");
    assertTrue(t.queryType().toString().equals("c → e"));
    assertTrue(t.toString().equals("f⟨aa, y⟩"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsFunctionSymbolWithoutTypeExpected() {
    Term t = readTerm("f⟨aa⟩", null, false, null, "1:1: Unexpected meta-application with " +
      "meta-variable f, which was previously declared as a function symbol.\n");
    assertTrue(t.queryType().toString().equals("o"));
    assertTrue(t.toString().equals("f⟨aa⟩"));
  }

  @Test
  public void testMetaVariableAlreadyDeclaredAsVariable() {
    SymbolData data = generateSignature();
    data.addVariable(TermFactory.createVar("Z", type("a → a")));
    data.addVariable(TermFactory.createVar("x", type("b")));
    Term t = readTerm("Z[x]", "b", false, data,
      "1:1: Unexpected meta-application with meta-variable Z, which was previously used " +
      "(or declared) as a variable without meta-arguments.\n");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("b"));
    assertTrue(data.lookupVariable("Z").queryType().toString().equals("a → a"));
    assertTrue(data.lookupMetaVariable("Z").queryType().toString().equals("b → b"));
  }

  @Test
  public void testMetaVariableDeclaredWithGreaterArity() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a → a"), 2));
    Term t = readTerm("Z[x]", "zot", true, data,
      "1:1: Meta-variable Z was previously used (or declared) with arity 2, but is here used " +
      "with 1 arguments.\n");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x⟩"));
    assertTrue(t.queryType().toString().equals("zot"));
    assertTrue(data.lookupVariable("x") == null);
    assertTrue(t.queryMetaVariable().queryType().toString().equals("o → zot"));
  }

  @Test
  public void testMetaVariableDeclaredWithSmallerArity() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a → a"), 1));
    Term t = readTerm("Z⟨aa,y⟩", null, true, data,
      "1:1: Meta-variable Z was previously used (or declared) with arity 1, but is here used " +
      "with 2 arguments.\n");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa, y⟩"));
    assertTrue(t.queryType().toString().equals("a → a"));
    assertTrue(t.queryMetaVariable().queryType().toString().equals("a → o → a → a"));
  }

  @Test
  public void testCorrectMultiApplicationWithMetaVariableDeclared() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → a → a"), 2));
    Term t = readTerm("Z⟨x,y⟩", "a", false, data, "");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨x, y⟩"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(data.lookupVariable("y").queryType().toString().equals("a"));
  }

  @Test
  public void testReadNestedMeta() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Y", type("a → b"), 1));
    Term t = readTerm("Z⟨aa,Y[x⟩,cc]", "d", true, data, "");
    assertTrue(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa, Y⟨x⟩, cc⟩"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("a"));
    assertTrue(data.lookupMetaVariable("Z").queryType().toString().equals("a → b → c → d"));
  }

  @Test
  public void testAppliedMetaApplication() {
    SymbolData data = generateSignature();
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → b → c → d"), 1));
    Term t = readTerm("Z⟨aa⟩(bb,cc)", "d", true, data, "");
    assertFalse(t.isMetaApplication());
    assertTrue(t.toString().equals("Z⟨aa⟩(bb, cc)"));
  }

  @Test
  public void testReadSimpleNot() {
    Term t = readTerm("¬x", null, true, null, "");
    assertTrue(t.isFunctionalTerm());
    assertTrue(t.queryRoot().isTheorySymbol());
    assertTrue(t.vars().size() == 1);
    assertTrue(t.toString().equals("¬x"));
  }

  @Test
  public void testMostlySimpleMinus() {
    Term t = readTerm("- (3+x)", null, true, null, "");
    assertTrue(t.toString().equals("-(3 + x)"));
    assertTrue(t.queryType().toString().equals("Int"));
  }

  @Test
  public void testDuplicateNot() {
    Term t = readTerm("¬¬ ( x > 0)", null, true, null, "");
    assertTrue(t.toString().equals("¬(¬(x > 0))"));
  }

  @Test
  public void testBadBracketOmission() {
    Term t = readTerm("¬ x > 0", "Bool", true, null,
      "1:1: Type error: expected term of type Int, but got ¬x of type Bool.\n");
    assertTrue(t.toString().equals("¬x > 0"));
  }

  @Test
  public void testReadSimpleInfix() {
    Term t = readTerm("1+2", null, true, null, "");
    assertTrue(t.toString().equals("1 + 2"));
    assertTrue(t.queryType().toString().equals("Int"));
  }

  @Test
  public void testReadInfixWithLeftToRightPriority() {
    Term t = readTerm("1/2+3  > x", null, true, null, "");
    assertTrue(t.toString().equals("1 / 2 + 3 > x"));
    assertTrue(t.vars().size() == 1);
    assertTrue(t.queryType().toString().equals("Bool"));
  }

  @Test
  public void testReadInfixWithRightToLeftPriority() {
    Term t = readTerm("x >= 3 + y * 2", null, true, null, "");
    assertTrue(t.toString().equals("x ≥ 3 + y * 2"));
    assertTrue(t.vars().size() == 2);
    assertTrue(t.queryType().toString().equals("Bool"));
  }

  @Test
  public void testReadNegativeInteger() {
    Term t = readTerm("-  5", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.createValue(-5)));
  }

  @Test
  public void testMinusBeforeAddition() {
    Term t = readTerm("- x + y", "Int", true, null, "");
    assertTrue(t.toString().equals("-x + y"));
    assertTrue(t.queryRoot().toString().equals("[+]"));
    assertTrue(t.queryArgument(1).queryRoot().toString().equals("[-]"));
  }

  @Test
  public void testNegativeIntegerInModulo() {
    Term t = readTerm("-2%1", null, true, null, "");
    assertTrue(t.toString().equals("-2 % 1"));
    assertTrue(t.queryRoot().toString().equals("[%]"));
    assertTrue(t.queryArgument(1).queryRoot().toString().equals("-2"));
  }

  @Test
  public void testReadSimpleMinusWithNegation() {
    Term t = readTerm("x - y", null, true, null, "");
    // this becomes: x + -y
    assertTrue(t.toString().equals("x - y"));
    assertTrue(t.queryRoot().toString().equals("[+]"));
    assertTrue(t.queryArgument(2).queryRoot().toString().equals("[-]"));
  }

  @Test
  public void testReadSimpleMinusWithConstant() {
    Term t = readTerm("x - 3", null, true, null, "");
    assertTrue(t.toString().equals("x - 3"));
    assertTrue(t.queryRoot().toString().equals("[+]"));
    assertTrue(t.queryArgument(2).queryRoot().toString().equals("-3"));
  }

  @Test
  public void testReadComplexMinuses() {
    Term t = readTerm("x -3 * 5 + 1 < -1-y", null, true, null, "");
    assertTrue(t.toString().equals("x - 3 * 5 + 1 < -1 - y"));
    assertTrue(t.vars().size() == 2);
    assertTrue(t.queryArgument(1).queryArgument(1).toString().equals("x - 3 * 5"));
    assertTrue(t.queryArgument(1).queryArgument(1).queryArgument(2).toString().equals("-(3 * 5)"));
  }

  @Test
  public void testMixedInfixPriorities() {
    SymbolData data = generateSignature();
    data.addFunctionSymbol(TermFactory.createConstant("q", type("b → Int")));
    data.addMetaVariable(TermFactory.createMetaVar("Z", type("a → Int"), 1));
    Term t = readTerm("q(x) < y /\\ y > Z[aa] + -13 * z +9", "Bool", true, data, "");
    assertTrue(t.isFunctionalTerm());
    assertFalse(t.isTheoryTerm());
    assertTrue(t.toString().equals("q(x) < y ∧ y > Z⟨aa⟩ + -13 * z + 9"));
    assertTrue(data.lookupVariable("x").queryType().toString().equals("b"));
    assertTrue(data.lookupVariable("z").queryType().toString().equals("Int"));
  }

  @Test
  public void testDoublePlus() {
    SymbolData data = generateSignature();
    Term t = readTerm("1 ++2", null, true, data,
      "1:4: Expected term, started by an identifier, λ, string or (, but got PLUS (+).\n");
    assertTrue(t == null);
  }

  @Test
  public void testReadPrefixMinus() {
    Term t = readTerm("[-]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.minusSymbol));
    t = readTerm("[-]", "Int → Bool → Int", true, null,
      "1:2: Use of unary calculation symbol [-] with binary type: while a - b is allowed to " +
      "occur in terms, this is considered syntactic sugar for a + (-b); it cannot be done in " +
      "a partially applied way.  If you want to use binary subtraction, please encode it using " +
      "a helper function symbol.\n");
    assertTrue(t.queryType().toString().equals("Int → Bool → Int"));
    t = readTerm("[-](3)", null, true, null, "");
    assertTrue(t.toString().equals("-3"));
    assertFalse(t.isApplication());
    t = readTerm("[-](3, 4)", null, true, null, "");
    assertTrue(t.toString().equals("3 - 4"));
    t = readTerm("[-](3, 4, 5)", null, true, null,
      "1:2: Arity error: [-] can be used either with 1 or 2 arguments, but here it occurs " +
      "with 3.\n");
  }

  @Test
  public void testReadInfixDiv() {
    Term t = readTerm("[/]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.divSymbol));
    t = readTerm("[/](3)", null, true, null, "");
    assertTrue(t.toString().equals("[/](3)"));
    t = readTerm("[/](3, 4)", null, true, null, "");
    assertTrue(t.toString().equals("3 / 4"));
  }

  @Test
  public void testReadEqualityTwoArgs() {
    // when given =_Int (or !=_Int), the type is fixed so the types of arguments do not need to be
    // derived
    SymbolData data = generateSignature();
    Term t = readTerm("x =_Int y", null, true, data, "");
    assertTrue(t.queryType().equals(type("Bool")));
    assertTrue(data.lookupVariable("x").queryType().equals(type("Int")));
    assertTrue(t.toString().equals("x = y"));
    // when given != (or =), the types of the arguments need to be derived, but if the first is
    // derivable, that's good enough
    t = readTerm("x != z", null, true, data, "");
    assertTrue(t.queryType().equals(type("Bool")));
    assertTrue(data.lookupVariable("z").queryType().equals(type("Int")));
    assertTrue(t.toString().equals("x ≠ z"));
    // same if the second is derivable!
    t = readTerm("u = \"test\"", null, true, data, "");
    assertTrue(t.queryType().equals(type("Bool")));
    assertTrue(data.lookupVariable("u").queryType().toString().equals("String"));
    assertTrue(t.toString().equals("u = \"test\""));
    // this also works for booleans
    t = readTerm("v != false", null, true, data, "");
    assertTrue(t.toString().equals("v ⊻ false"));
    assertTrue(data.lookupVariable("v").queryType().toString().equals("Bool"));
    // and if the type cannot be derived, we have an appropriate error
    t = readTerm("a != b", "Bool", true, null,
      "1:3: Cannot deduce input type of overloaded operator.  " +
      "Please indicate the type by subscripting (e.g., !=_Int).\n");
    assertTrue(t.toString().equals("[!=](a, b)"));
  }

  @Test
  public void testReadCorrectEqualityOneArg() {
    // when given !=_Int (or =_Int), the type is fixed so the types of arguments do not need to be
    // derived
    SymbolData data = generateSignature();
    Term t = readTerm("[!=_Int](x)", null, true, data, "");
    assertTrue(t.queryType().equals(type("Int → Bool")));
    assertTrue(data.lookupVariable("x").queryType().equals(type("Int")));
    assertTrue(t.toString().equals("[≠](x)"));
    // when an expected type is given, this is used to derive the argument's type
    t = readTerm("[=](y)", "Bool → Bool", true, data, "");
    assertTrue(t.queryType().toString().equals("Bool → Bool"));
    assertTrue(data.lookupVariable("y").queryType().toString().equals("Bool"));
    assertTrue(t.queryRoot().equals(TheoryFactory.iffSymbol));
    // when given = (or !=), the types of the argument needs to be derived
    t = readTerm("[!=](\"test\")", null, true, data, "");
    assertTrue(t.queryType().equals(type("String → Bool")));
    assertTrue(t.toString().equals("[≠](\"test\")"));
    // and if the type cannot be derived, we have an appropriate error
    t = readTerm("[=](a)", null, true, null,
      "1:2: Cannot deduce input type of overloaded operator.  " +
      "Please indicate the type by subscripting (e.g., =_Int).\n");
    assertTrue(t.toString().equals("[=](a)"));
  }

  @Test
  public void testEqualityNoArg() {
    Term t;
    t = readTerm("[=]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.intEqualSymbol));
    t = readTerm("[=_Int]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.intEqualSymbol));
    t = readTerm("[=_String]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.stringEqualSymbol));
    t = readTerm("[=_Bool]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.iffSymbol));
    t = readTerm("[!=]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.intDistinctSymbol));
    t = readTerm("[!=_Int]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.intDistinctSymbol));
    t = readTerm("[!=_String]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.stringDistinctSymbol));
    t = readTerm("[!=_Bool]", null, true, null, "");
    assertTrue(t.equals(TheoryFactory.xorSymbol));
  }

  @Test
  public void testReadIncorrectEquality() {
    readTerm("\"hello\" = 3", null, true, null,
      "1:11: Expected term of type String, but got value 3 which has type Int.\n");
    readTerm("[=](4)", "String -> Bool", true, null,
      "1:5: Expected term of type String, but got value 4 which has type Int.\n");
    readTerm("[=](1, 2, 3)", null, true, null,
      "1:2: Arity error: overloaded operator = can take 2 arguments, but 3 are given!\n");
  }
}

