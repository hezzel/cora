/**************************************************************************************************
 Copyright 2020 Cynthia Kop

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
import org.antlr.v4.runtime.tree.ParseTree;
import java.util.ArrayList;
import java.util.TreeMap;

import cora.exceptions.ParserException;
import cora.exceptions.DeclarationException;
import cora.exceptions.TypingException;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Position;
import cora.interfaces.rewriting.Rule;
import cora.interfaces.rewriting.TRS;
import cora.types.Sort;
import cora.types.ArrowType;
import cora.terms.Var;
import cora.terms.BinderVariable;
import cora.terms.Constant;
import cora.terms.FunctionalTerm;
import cora.terms.Abstraction;
import cora.parsers.ErrorCollector;
import cora.parsers.ParseData;
import cora.parsers.HrsParser;
import cora.parsers.HrsInputReader;

public class HrsReadingTest {
  private ParseData createParseData() {
    ParseData data = new ParseData();
    data.addFunctionSymbol(new Constant("0", new Sort("Nat")));
    data.addFunctionSymbol(new Constant("suc", new ArrowType(new Sort("Nat"), new Sort("Nat"))));
    data.addFunctionSymbol(new Constant("nil", new Sort("List")));
    data.addFunctionSymbol(new Constant("cons",
      new ArrowType(new Sort("Nat"), new ArrowType(new Sort("List"), new Sort("List")))));
    data.addVariable(new Var("x", new Sort("Nat")));
    data.addVariable(new Var("y", new Sort("List")));
    return data;
  }
  
  @Test
  public void testReadBaseType() throws ParserException {
    Type type = HrsInputReader.readTypeFromString("a");
    assertTrue(type.equals(new Sort("a")));
  }

  @Test
  public void testReadArrowType() throws ParserException {
    Type type = HrsInputReader.readTypeFromString("a -> b");
    assertTrue(type.isArrowType());
    assertTrue(type.queryArrowInputType().equals(new Sort("a")));
    assertTrue(type.queryArrowOutputType().equals(new Sort("b")));
  }

  @Test
  public void testReadBaseTypeWithBrackets() throws ParserException {
    Type type = HrsInputReader.readTypeFromString("(a)");
    assertTrue(type.equals(new Sort("a")));
  }

  @Test
  public void testReadArrowTypeWithBrackets() throws ParserException {
    Type type = HrsInputReader.readTypeFromString("(a -> b) -> c");
    assertTrue(type.isArrowType());
    assertTrue(type.queryArrowInputType().isArrowType());
    assertTrue(type.queryArrowInputType().queryArrowInputType().equals(new Sort("a")));
    assertTrue(type.queryArrowInputType().queryArrowOutputType().equals(new Sort("b")));
    assertTrue(type.queryArrowOutputType().equals(new Sort("c")));
  }

  @Test
  public void testExtendedReadType() throws ParserException {
    Type type = HrsInputReader.readTypeFromString("a->b->(c->d->e)->f->g");
    assertTrue(type.isArrowType());
    assertTrue(type.queryArrowInputType().equals(new Sort("a")));
    Type bcdefg = type.queryArrowOutputType();
    assertTrue(bcdefg.isArrowType());
    assertTrue(bcdefg.queryArrowInputType().equals(new Sort("b")));
    Type cdefg = bcdefg.queryArrowOutputType();
    assertTrue(cdefg.isArrowType());
    Type cde = cdefg.queryArrowInputType();
    Type fg = cdefg.queryArrowOutputType();
    assertTrue(cde.isArrowType());
    assertTrue(cde.queryArrowInputType().equals(new Sort("c")));
    assertTrue(cde.queryArrowOutputType().queryArrowInputType().equals(new Sort("d")));
    assertTrue(cde.queryArrowOutputType().queryArrowOutputType().equals(new Sort("e")));
    assertTrue(fg.isArrowType());
    assertTrue(fg.queryArrowInputType().equals(new Sort("f")));
    assertTrue(fg.queryArrowOutputType().equals(new Sort("g")));
  }

  @Test
  public void testReadSignatureVF() throws ParserException {
    ParseData data = HrsInputReader.readSignatureFromStringUT(
      "(VAR x : a y : b -> c z : d) (FUN f : a)");
    assertTrue(data.queryNumberVariables() == 3);
    assertTrue(data.queryNumberFunctionSymbols() == 1);
    assertTrue(data.lookupVariable("x").queryType().equals(new Sort("a")));
    assertTrue(data.lookupVariable("y").queryType().equals(
      new ArrowType(new Sort("b"), new Sort("c"))));
    assertTrue(data.lookupVariable("z").queryType().equals(new Sort("d")));
    assertTrue(data.lookupFunctionSymbol("f").queryType().equals(new Sort("a")));
  }

  @Test
  public void testReadSignatureFV() throws ParserException {
    ParseData data = HrsInputReader.readSignatureFromStringUT(
      "(FUN x : a y : b) (VAR f : a)");
    assertTrue(data.queryNumberVariables() == 1);
    assertTrue(data.queryNumberFunctionSymbols() == 2);
    assertTrue(data.lookupFunctionSymbol("x").queryType().equals(new Sort("a")));
    assertTrue(data.lookupFunctionSymbol("y").queryType().equals(new Sort("b")));
    assertTrue(data.lookupVariable("f").queryType().equals(new Sort("a")));
  }

  @Test(expected = cora.exceptions.ParserException.class)
  public void testSignatureConflict() throws ParserException {
    HrsInputReader.readSignatureFromStringUT("(FUN a : b) (VAR a : b)");
  }

  @Test
  public void testReadConstant() throws ParserException {
    ParseData data = createParseData();
    Term t = HrsInputReader.readTermFromString("0", data);
    assertTrue(t.equals(data.lookupFunctionSymbol("0")));
  }

  @Test
  public void testReadVariable() throws ParserException {
    ParseData data = createParseData();
    Term t = HrsInputReader.readTermFromString("x", data);
    assertTrue(t.equals(data.lookupVariable("x")));
  }

  @Test
  public void testApplication() throws ParserException {
    ParseData data = createParseData();
    Term t = HrsInputReader.readTermFromString("suc 0", data);
    assertTrue(t.toString().equals("suc(0)"));
  }

  @Test
  public void testAbstraction() throws ParserException {
    ParseData data = createParseData();
    Term t = HrsInputReader.readTermFromString("\\x.suc x", data);
    assertTrue(t.isAbstraction());
    Variable y = t.queryVariable();
    assertTrue(y.isBinderVariable());
    Term sub = t.queryImmediateSubterm(1);
    assertTrue(sub.queryRoot().equals(data.lookupFunctionSymbol("suc")));
    assertTrue(sub.queryImmediateSubterm(1).equals(y));
  }

  @Test
  public void testMultipleAbstraction() throws ParserException {
    ParseData data = createParseData();
    Term t = HrsInputReader.readTermFromString("\\x y.cons x y", data);
    assertTrue(t.isAbstraction());
    Variable x = t.queryVariable();
    assertTrue(x.isBinderVariable());
    Term s = t.queryImmediateSubterm(1);
    assertTrue(s.isAbstraction());
    Variable y = s.queryVariable();
    Term sub = s.queryImmediateSubterm(1);
    assertTrue(sub.equals(new FunctionalTerm(data.lookupFunctionSymbol("cons"), x, y)));
  }

  @Test(expected = cora.exceptions.ParserException.class)
  public void testBadAbstraction() throws ParserException {
    ParseData data = createParseData();
    HrsInputReader.readTermFromString("\\x x.suc 0", data);
  }

  @Test
  public void testFunctionalTerm() throws ParserException {
    ParseData data = createParseData();
    Term t = HrsInputReader.readTermFromString("cons(0, nil)", data);
    assertTrue(t.toString().equals("cons(0, nil)"));
  }

  @Test
  public void testIckyApplication() throws ParserException {
    ParseData data = createParseData();
    Term t = HrsInputReader.readTermFromString("suc suc suc 0", data);
    assertTrue(t.toString().equals("suc(suc(suc(0)))"));
  }

  @Test
  public void testMixedTerm() throws ParserException {
    ParseData data = createParseData();
    data.addFunctionSymbol(new Constant("map", HrsInputReader.readTypeFromString(
      "(Nat -> Nat) -> List -> List")));
    Term t = HrsInputReader.readTermFromString("map(\\x.suc(x), cons(0)nil)", data);

    Variable x = new BinderVariable("x", new Sort("Nat"));
    Term sucx = new FunctionalTerm(data.lookupFunctionSymbol("suc"), x);
    assertTrue(t.queryImmediateSubterm(1).equals(new Abstraction(x, sucx)));
    assertTrue(t.queryImmediateSubterm(2).toString().equals("cons(0, nil)"));
  }

  @Test(expected = cora.exceptions.ParserException.class)
  public void testUntypableTerm() throws ParserException {
    ParseData data = createParseData();
    Term t = HrsInputReader.readTermFromString("cons suc 0 suc nil", data);
  }
}

