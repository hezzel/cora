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
import cora.parsers.ParseData;
import cora.exceptions.TypingError;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Alphabet;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.types.Sort;
import cora.terms.Constant;
import cora.terms.Var;
import cora.terms.UserDefinedAlphabet;
import cora.rewriting.TermRewritingSystem;

/** This class tests the antlr code for parsing types. */

public class ParseDataTest {
  @Test
  public void testBasics() {
    ParseData data = new ParseData();
    Constant bing = new Constant("bing", new Sort("a"));
    Var bong = new Var("bong", new Sort("b"));
    data.addFunctionSymbol(bing);
    assertTrue(data.lookupFunctionSymbol("bing").equals(bing));
    assertTrue(data.lookupFunctionSymbol("a") == null);
    data.addVariable(bong);
    assertTrue(data.lookupVariable("bong").equals(bong));
    assertTrue(data.lookupVariable("bing") == null);
    data.clearVariables();
    assertTrue(data.lookupVariable("bong") == null);
  }

  @Test
  public void testCounts() {
    ParseData data = new ParseData();
    Constant bing = new Constant("bing", new Sort("a"));
    Var bongv = new Var("bong", new Sort("b"));
    Constant bongf = new Constant("bong", new Sort("a"));
    data.addFunctionSymbol(bing);
    data.addFunctionSymbol(bongf);
    data.addFunctionSymbol(bing);
    assertTrue(data.queryNumberFunctionSymbols() == 2);
    assertTrue(data.queryNumberVariables() == 0);
    data.addVariable(bongv);
    assertTrue(data.queryNumberFunctionSymbols() == 2);
    assertTrue(data.queryNumberVariables() == 1);
  }

  @Test
  public void testEqualVariableAndFunction() {
    ParseData data = new ParseData();
    Constant bing1 = new Constant("bing", new Sort("a"));
    Var bing2 = new Var("bing", new Sort("b"));
    data.addFunctionSymbol(bing1);
    data.addVariable(bing2);
    assertTrue(data.lookupFunctionSymbol("bing").equals(bing1));
    assertTrue(data.lookupVariable("bing").equals(bing2));
  }

  @Test
  public void testLookupNonExisting() {
    ParseData data = new ParseData();
    data.addFunctionSymbol(new Constant("bing", new Sort("a")));
    assertTrue(data.lookupFunctionSymbol("bong") == null);
    assertTrue(data.lookupVariable("bing") == null);
  }

  @Test
  public void testFunctionSymbolLegalOverride() {
    ParseData data = new ParseData();
    data.addFunctionSymbol(new Constant("bing", new Sort("a")));
    data.addFunctionSymbol(new Constant("bing", new Sort("a")));
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
    data.addFunctionSymbol(new Constant("bing", new Sort("a")));
    data.addFunctionSymbol(new Constant("bing", new Sort("b")));
  }

  @Test(expected = java.lang.Error.class)
  public void testVariableIllegalOverride() {
    ParseData data = new ParseData();
    //  variables with the same name and type are not equal if they are different objects
    data.addVariable(new Var("bing", new Sort("a")));
    data.addVariable(new Var("bing", new Sort("a")));
  }

  @Test
  public void testGenerateAlphabet() {
    ParseData data = new ParseData();
    Constant bing = new Constant("bing", new Sort("a"));
    Constant bong = new Constant("bong", new Sort("a"));
    Var bang = new Var("bang", new Sort("b"));
    data.addFunctionSymbol(bing);
    data.addFunctionSymbol(bong);
    data.addFunctionSymbol(bing);
    data.addVariable(bang);
    Alphabet alf = data.queryCurrentAlphabet();
    assertTrue(alf.lookup("bing").equals(bing));
    assertTrue(alf.lookup("bong").equals(bong));
    assertTrue(alf.lookup("bang") == null);
    Constant bangf = new Constant("bang", new Sort("a"));
    data.addFunctionSymbol(bangf);
    assertTrue(alf.lookup("bang") == null);
  }

  @Test
  public void testInitialiseWithTRS() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    FunctionSymbol bing = new Constant("bing", new Sort("a"));
    FunctionSymbol bong = new Constant("bong", new Sort("b"));
    symbols.add(bing);
    UserDefinedAlphabet alf = new UserDefinedAlphabet(symbols);
    TRS trs = new TermRewritingSystem(alf, new ArrayList<Rule>());
    ParseData data = new ParseData(trs);

    assertTrue(data.lookupFunctionSymbol("bing").equals(bing));
    assertTrue(data.lookupVariable("bing") == null);

    data.addFunctionSymbol(bong);

    assertTrue(data.lookupFunctionSymbol("bing").equals(bing));
    assertTrue(data.lookupFunctionSymbol("bong").equals(bong));
  }

  @Test(expected =  java.lang.Error.class)
  public void testVariableIllegalOverrideInAlphabet() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    FunctionSymbol bing = new Constant("bing", new Sort("a"));
    symbols.add(bing);
    UserDefinedAlphabet alf = new UserDefinedAlphabet(symbols);
    TRS trs = new TermRewritingSystem(alf, new ArrayList<Rule>());
    ParseData data = new ParseData(trs);

    FunctionSymbol bong = new Constant("bing", new Sort("b"));
    data.addFunctionSymbol(bong);
  }
}

