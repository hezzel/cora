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
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.rewriting.Rule;
import cora.core.types.Sort;
import cora.core.types.ArrowType;
import cora.core.terms.UserDefinedSymbol;
import cora.core.terms.Var;
import cora.parsers.ParseData;
import cora.parsers.CoraInputReader;

public class ProgramReadingTest {
  @Test
  public void testReadDeclaration() throws ParserException {
    ParseData sigma = new ParseData();
    String str = "0 :: N s :: N -> N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))";
    CoraInputReader.readProgramFromString(str, sigma);
    assertTrue(sigma.queryNumberFunctionSymbols() == 3);
    FunctionSymbol nul = sigma.lookupFunctionSymbol("0");
    FunctionSymbol suc = sigma.lookupFunctionSymbol("s");
    FunctionSymbol add = sigma.lookupFunctionSymbol("add");
    assertTrue(nul.queryType().toString().equals("N"));
    assertTrue(suc.queryType().toString().equals("N → N"));
    assertTrue(add.queryType().toString().equals("N → N → N"));
  }

  @Test
  public void testSimpleProgram() throws ParserException {
    ParseData sigma = new ParseData();
    sigma.addFunctionSymbol(new UserDefinedSymbol("0", new Sort("N")));
    sigma.addFunctionSymbol(new UserDefinedSymbol("s",
        new ArrowType(new Sort("N"), new Sort("N"))));
    sigma.addFunctionSymbol(new UserDefinedSymbol("add", new ArrowType(new Sort("N"),
        new ArrowType(new Sort("N"), new Sort("N")))));
    String str = "add(0,y) -> y add(s(x),y) -> s(add(x,y))";
    ArrayList<Rule> rules = CoraInputReader.readProgramFromString(str, sigma);
    assertTrue(rules.size() == 2);
    assertTrue(rules.get(0).toString().equals("add(0, y) → y"));
    assertTrue(rules.get(1).toString().equals("add(s(x), y) → s(add(x, y))"));
  }

  @Test
  public void testNoRemainingVariables() throws ParserException {
    ParseData sigma = new ParseData();
    String str = "0 :: N s :: N -> N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))";
    CoraInputReader.readProgramFromString(str, sigma);
    assertTrue(sigma.queryNumberVariables() == 0);
  }

  @Test(expected = cora.exceptions.DeclarationException.class)
  public void testUndeclaredSymbol() throws ParserException {
    ParseData sigma = new ParseData();
    String str = "0 :: N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))";
    CoraInputReader.readProgramFromString(str, sigma);
  }

  @Test(expected = Error.class)
  public void testParseDataHasVariables() throws ParserException {
    ParseData sigma = new ParseData();
    sigma.addVariable(new Var("x", new Sort("a")));
    String str = "0 :: N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))";
    CoraInputReader.readProgramFromString(str, sigma);
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadRuleWithInconsistentTypes() throws ParserException {
    ParseData sigma = new ParseData();
    String str = "a :: type1 b :: type2 a -> b";
    CoraInputReader.readProgramFromString(str, sigma);
  }
}

