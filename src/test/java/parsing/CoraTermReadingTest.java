/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsers;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.ParserException;
import cora.exceptions.AntlrParserException;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.Term;
import cora.terms.Variable;
import cora.terms.FunctionSymbol;
import cora.terms.TermFactory;

public class CoraTermReadingTest {
  private FunctionSymbol generateSymbol(String name, String type) throws ParserException {
    return TermFactory.createConstant(name, CoraInputReader.readTypeFromString(type));
  }

  private ParseData generateSignature() throws ParserException {
    ParseData data = new ParseData();
    data.addFunctionSymbol(generateSymbol("f", "a -> b -> c -> d"));
    data.addFunctionSymbol(generateSymbol("aa", "a"));
    data.addFunctionSymbol(generateSymbol("bb", "b"));
    data.addFunctionSymbol(generateSymbol("cc", "c"));
    data.addFunctionSymbol(generateSymbol("h", "(c -> d) -> b"));
    return data;
  }

  @Test
  public void testReadUndeclaredVariableWithType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("xx_yy", sigma, TypeFactory.createSort("v"));
    Variable x = sigma.lookupVariable("xx_yy");
    assertTrue(x != null);
    assertTrue(x.queryType().equals(TypeFactory.createSort("v")));
    assertTrue(x.queryName().equals("xx_yy"));
    assertTrue(term.equals(x));
  }

  @Test(expected = cora.exceptions.DeclarationException.class)
  public void testReadUndeclaredVariableWithoutType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("xx_yy", sigma, null);
    Variable x = sigma.lookupVariable("xx_yy");
  }

  @Test
  public void testReadDeclaredVariableWithCorrectType() throws ParserException {
    ParseData sigma = generateSignature();
    Variable x = TermFactory.createVar("x", TypeFactory.createSort("a"));
    sigma.addVariable(x);
    Term term = CoraInputReader.testReadTermFromString("x", sigma, TypeFactory.createSort("a"));
    assertTrue(term.equals(x));
    assertTrue(sigma.lookupVariable("x").equals(x));
  }

  @Test
  public void testReadDeclaredVariableWithoutType() throws ParserException {
    ParseData sigma = generateSignature();
    Variable x = TermFactory.createVar("x", TypeFactory.createSort("a"));
    sigma.addVariable(x);
    Term term = CoraInputReader.testReadTermFromString("x", sigma, null);
    assertTrue(term.equals(x));
    assertTrue(sigma.lookupVariable("x").equals(x));
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadDeclaredVariableWithIncorrectType() throws ParserException {
    ParseData sigma = generateSignature();
    Variable x = TermFactory.createVar("x", TypeFactory.createSort("b"));
    sigma.addVariable(x);
    Term term = CoraInputReader.testReadTermFromString("x", sigma, TypeFactory.createSort("a"));
  }

  @Test
  public void testReadBaseConstantWithoutType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("aa", sigma, null);
    assertTrue(term.equals(generateSymbol("aa", "a")));
  }

  @Test
  public void testReadBaseConstantWithGoodType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("aa", sigma, TypeFactory.createSort("a"));
    assertTrue(term.equals(generateSymbol("aa", "a")));
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadBaseConstantWithBadType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("aa", sigma, TypeFactory.createSort("b"));
  }

  @Test
  public void testReadHigherOrderConstant() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f", sigma, null);
    assertTrue(term.equals(generateSymbol("f", "a -> b -> c -> d")));
  }

  @Test
  public void testReadEmptyApplicationOfConstantWithType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("bb()", sigma, TypeFactory.createSort("b"));
    assertTrue(term.equals(generateSymbol("bb", "b")));
  }

  @Test
  public void testReadEmptyApplicationOfConstantWithoutType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f()", sigma, null);
    assertTrue(term.equals(generateSymbol("f", "a -> b -> c -> d")));
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testEmptyApplicationWithIncorrectType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f()", sigma, TypeFactory.createSort("d"));
  }

  @Test
  public void testReadFullApplication() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f(aa,bb, cc)", sigma, null);
    FunctionSymbol f = generateSymbol("f", "a -> b -> c -> d");
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(generateSymbol("aa", "a"));
    args.add(generateSymbol("bb", "b"));
    args.add(generateSymbol("cc", "c"));
    assertTrue(term.equals(TermFactory.createApp(f, args)));
    assertTrue(term.queryType().equals(TypeFactory.createSort("d")));
  }

  @Test
  public void testReadIncompleteApplication() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f(aa, x)", sigma, null);
    Variable x = sigma.lookupVariable("x");
    assertTrue(x.queryType().equals(TypeFactory.createSort("b")));
    assertTrue(term.queryType().queryArrowInputType().equals(TypeFactory.createSort("c")));
    assertTrue(term.queryType().queryArrowOutputType().equals(TypeFactory.createSort("d")));
    assertTrue(term.queryRoot().equals(generateSymbol("f", "a -> b -> c -> d")));
    assertTrue(term.queryArgument(1).equals(generateSymbol("aa", "a")));
    assertTrue(term.queryArgument(2).equals(x));
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadApplicationWithIncorrectTypes() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f(aa, bb, bb)", sigma, null);
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadApplicationWithInconsistentVariables() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f(x, bb, x)", sigma, null);
  }

  @Test
  public void testPartiallyAppliedSubterm() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f(x,h(f(x, bb)),cc)", sigma, null);
    assertTrue(term.toString().equals("f(x, h(f(x, bb)), cc)"));
  }

  @Test
  public void testReadDeclaredVariableApplication() throws ParserException {
    ParseData sigma = generateSignature();
    sigma.addVariable(TermFactory.createVar("Z",
                        CoraInputReader.readTypeFromString("a -> b -> c")));
    Term term = CoraInputReader.testReadTermFromString("Z( aa,x )", sigma, null);
    assertTrue(term.queryType().equals(TypeFactory.createSort("c")));
    assertTrue(term.toString().equals("Z(aa, x)"));
  }

  @Test(expected = cora.exceptions.DeclarationException.class)
  public void testReadUndeclaredVariableApplication() throws ParserException {
    ParseData sigma = generateSignature();
    // it's not allowed, even if the type can be found from context
    Term term = CoraInputReader.testReadTermFromString("Z(aa)", sigma, TypeFactory.createSort("b"));
  }

  @Test(expected = cora.exceptions.AntlrParserException.class)
  public void testMissingBracket() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f(x,h(f(x, bb),cc)", sigma, null);
  }

  @Test(expected = cora.exceptions.AntlrParserException.class)
  public void testMissingComma() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.testReadTermFromString("f(x,h(f(x, bb)) cc)", sigma, null);
  }
}

