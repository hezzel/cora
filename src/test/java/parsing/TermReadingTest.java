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
import cora.exceptions.ParserException;
import cora.exceptions.AntlrParserException;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.FunctionSymbol;
import cora.types.Sort;
import cora.terms.UserDefinedSymbol;
import cora.terms.FunctionalTerm;
import cora.terms.Var;
import cora.parsers.ParseData;
import cora.parsers.CoraInputReader;

public class TermReadingTest {
  private FunctionSymbol generateSymbol(String name, String type) throws ParserException {
    return new UserDefinedSymbol(name, CoraInputReader.readTypeFromString(type));
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
    Term term = CoraInputReader.readTermFromString("xx_yy", sigma, new Sort("varsort"));
    Variable x = sigma.lookupVariable("xx_yy");
    assertTrue(x != null);
    assertTrue(x.queryType().equals(new Sort("varsort")));
    assertTrue(x.queryName().equals("xx_yy"));
    assertTrue(term.equals(x));
  }

  @Test(expected = cora.exceptions.DeclarationException.class)
  public void testReadUndeclaredVariableWithoutType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("xx_yy", sigma, null);
    Variable x = sigma.lookupVariable("xx_yy");
  }

  @Test
  public void testReadDeclaredVariableWithCorrectType() throws ParserException {
    ParseData sigma = generateSignature();
    Variable x = new Var("x", new Sort("a"));
    sigma.addVariable(x);
    Term term = CoraInputReader.readTermFromString("x", sigma, new Sort("a"));
    assertTrue(term.equals(x));
    assertTrue(sigma.lookupVariable("x").equals(x));
  }

  @Test
  public void testReadDeclaredVariableWithoutType() throws ParserException {
    ParseData sigma = generateSignature();
    Variable x = new Var("x", new Sort("a"));
    sigma.addVariable(x);
    Term term = CoraInputReader.readTermFromString("x", sigma, null);
    assertTrue(term.equals(x));
    assertTrue(sigma.lookupVariable("x").equals(x));
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadDeclaredVariableWithIncorrectType() throws ParserException {
    ParseData sigma = generateSignature();
    Variable x = new Var("x", new Sort("b"));
    sigma.addVariable(x);
    Term term = CoraInputReader.readTermFromString("x", sigma, new Sort("a"));
  }

  @Test
  public void testReadBaseConstantWithoutType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("aa", sigma, null);
    assertTrue(term.equals(new FunctionalTerm(generateSymbol("aa", "a"))));
  }

  @Test
  public void testReadBaseConstantWithGoodType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("aa", sigma, new Sort("a"));
    assertTrue(term.equals(new FunctionalTerm(generateSymbol("aa", "a"))));
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadBaseConstantWithBadType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("aa", sigma, new Sort("b"));
  }

  @Test
  public void testReadHigherOrderConstant() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f", sigma, null);
    assertTrue(term.equals(new FunctionalTerm(generateSymbol("f", "a -> b -> c -> d"))));
  }

  @Test
  public void testReadEmptyApplicationOfConstantWithType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("bb()", sigma, new Sort("b"));
    assertTrue(term.equals(new FunctionalTerm(generateSymbol("bb", "b"))));
  }

  @Test
  public void testReadEmptyApplicationOfConstantWithoutType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f()", sigma, null);
    assertTrue(term.equals(new FunctionalTerm(generateSymbol("f", "a -> b -> c -> d"))));
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testEmptyApplicationWithIncorrectType() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f()", sigma, new Sort("d"));
  }

  @Test
  public void testReadFullApplication() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f(aa,bb, cc)", sigma, null);
    FunctionSymbol f = generateSymbol("f", "a -> b -> c -> d");
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new FunctionalTerm(generateSymbol("aa", "a")));
    args.add(new FunctionalTerm(generateSymbol("bb", "b")));
    args.add(new FunctionalTerm(generateSymbol("cc", "c")));
    assertTrue(term.equals(new FunctionalTerm(f, args)));
    assertTrue(term.queryType().equals(new Sort("d")));
  }

  @Test
  public void testReadIncompleteApplication() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f(aa, x)", sigma, null);
    Variable x = sigma.lookupVariable("x");
    assertTrue(x.queryType().equals(new Sort("b")));
    assertTrue(term.queryType().queryArrowInputType().equals(new Sort("c")));
    assertTrue(term.queryType().queryArrowOutputType().equals(new Sort("d")));
    assertTrue(term.queryRoot().equals(generateSymbol("f", "a -> b -> c -> d")));
    assertTrue(term.queryImmediateSubterm(1).equals(new FunctionalTerm(generateSymbol("aa", "a"))));
    assertTrue(term.queryImmediateSubterm(2).equals(x));
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadApplicationWithIncorrectTypes() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f(aa, bb, bb)", sigma, null);
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadApplicationWithInconsistentVariables() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f(x, bb, x)", sigma, null);
  }

  @Test
  public void testPartiallyAppliedSubterm() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f(x,h(f(x, bb)),cc)", sigma, null);
    assertTrue(term.toString().equals("f(x, h(f(x, bb)), cc)"));
  }

  @Test(expected = cora.exceptions.AntlrParserException.class)
  public void testMissingBracket() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f(x,h(f(x, bb),cc)", sigma, null);
  }

  @Test(expected = cora.exceptions.AntlrParserException.class)
  public void testMissingComma() throws ParserException {
    ParseData sigma = generateSignature();
    Term term = CoraInputReader.readTermFromString("f(x,h(f(x, bb)) cc)", sigma, null);
  }
}

