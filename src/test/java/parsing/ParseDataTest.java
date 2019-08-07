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
import cora.parsers.ParseData;
import cora.exceptions.TypingError;
import cora.immutabledata.types.Sort;
import cora.immutabledata.terms.UserDefinedSymbol;
import cora.immutabledata.terms.Var;

/** This class tests the antlr code for parsing types. */

public class ParseDataTest {
  @Test
  public void testBasics() {
    ParseData data = new ParseData();
    UserDefinedSymbol bing = new UserDefinedSymbol("bing", new Sort("a"));
    Var bong = new Var("bong", new Sort("b"));
    data.addFunctionSymbol(bing);
    assertTrue(data.lookupFunctionSymbol("bing").equals(bing));
    assertTrue(data.lookupFunctionSymbol("a") == null);
    data.addVariable(bong);
    assertTrue(data.lookupVariable("bong").equals(bong));
    assertTrue(data.lookupVariable("bing") == null);
  }

  @Test
  public void testEqualVariableAndFunction() {
    ParseData data = new ParseData();
    UserDefinedSymbol bing1 = new UserDefinedSymbol("bing", new Sort("a"));
    Var bing2 = new Var("bing", new Sort("b"));
    data.addFunctionSymbol(bing1);
    data.addVariable(bing2);
    assertTrue(data.lookupFunctionSymbol("bing").equals(bing1));
    assertTrue(data.lookupVariable("bing").equals(bing2));
  }

  @Test
  public void testLookupNonExisting() {
    ParseData data = new ParseData();
    data.addFunctionSymbol(new UserDefinedSymbol("bing", new Sort("a")));
    assertTrue(data.lookupFunctionSymbol("bong") == null);
    assertTrue(data.lookupVariable("bing") == null);
  }

  @Test
  public void testFunctionSymbolLegalOverride() {
    ParseData data = new ParseData();
    data.addFunctionSymbol(new UserDefinedSymbol("bing", new Sort("a")));
    data.addFunctionSymbol(new UserDefinedSymbol("bing", new Sort("a")));
    assertTrue(data.lookupFunctionSymbol("bing").queryType().equals(new Sort("a")));
  }

  @Test
  public void testVariableLegalOverride() {
    ParseData data = new ParseData();
    Var x = new Var("bing", new Sort("a"));
    data.addVariable(x);
    data.addVariable(x);
    assertTrue(data.lookupVariable("bing").queryType().equals(new Sort("a")));
  }

  @Test(expected = java.lang.Error.class)
  public void testFunctionSymbolIllegalOverride() {
    ParseData data = new ParseData();
    data.addFunctionSymbol(new UserDefinedSymbol("bing", new Sort("a")));
    data.addFunctionSymbol(new UserDefinedSymbol("bing", new Sort("b")));
  }

  @Test(expected = java.lang.Error.class)
  public void testVariableIllegalOverride() {
    ParseData data = new ParseData();
    //  variables with the same name and type are not equal if they are different objects
    data.addVariable(new Var("bing", new Sort("a")));
    data.addVariable(new Var("bing", new Sort("a")));
  }
}

