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
import cora.interfaces.rewriting.TRS;
import cora.core.types.Sort;
import cora.core.types.ArrowType;
import cora.core.terms.UserDefinedSymbol;
import cora.core.terms.Var;
import cora.parsers.ParseData;
import cora.parsers.CoraInputReader;

public class ProgramReadingTest {
  @Test
  public void testReadDeclaration() throws ParserException {
    String str = "0 :: N s :: N -> N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))";
    TRS trs = CoraInputReader.readProgramFromString(str);
    assertTrue(trs.lookupSymbol("0").queryType().toString().equals("N"));
    assertTrue(trs.lookupSymbol("s").queryType().toString().equals("N → N"));
    assertTrue(trs.lookupSymbol("add").queryType().toString().equals("N → N → N"));
  }

  @Test
  public void testSimpleProgram() throws ParserException {
    String str = "0 :: N s :: N -> N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))";
    TRS trs = CoraInputReader.readProgramFromString(str);
    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).toString().equals("add(0, y) → y"));
    assertTrue(trs.queryRule(1).toString().equals("add(s(x), y) → s(add(x, y))"));
  }

  @Test
  public void testNoVariableConflictsBetweenRules() throws ParserException {
    String str = "f :: a -> a  g :: b -> b f(x) -> x  g(x) -> x";
    CoraInputReader.readProgramFromString(str);
  }

  @Test(expected = cora.exceptions.DeclarationException.class)
  public void testUndeclaredSymbol() throws ParserException {
    String str = "0 :: N add :: N -> N -> N add(0,y) -> y add(s(x),y) -> s(add(x,y))";
    CoraInputReader.readProgramFromString(str);
  }

  @Test(expected = cora.exceptions.TypingException.class)
  public void testReadRuleWithInconsistentTypes() throws ParserException {
    String str = "a :: type1 b :: type2 a -> b";
    CoraInputReader.readProgramFromString(str);
  }
}

