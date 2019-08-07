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
import cora.exceptions.ArityError;
import cora.exceptions.IndexingError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Term;
import cora.immutabledata.types.*;
import cora.immutabledata.terms.*;

public class TermTest {
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
    FunctionSymbol f = new UserDefinedSymbol(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  private Term twoArgTerm() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new UserDefinedSymbol("f", type);
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")));
    return new FunctionalTerm(f, arg1, arg2);
  }

  @Test(expected = NullInitialisationError.class)
  public void testUnaryWithNullArg() {
    FunctionSymbol f = new UserDefinedSymbol("f", arrowType("a", "b"));
    Term arg = null;
    Term t = new FunctionalTerm(f, arg);
  }

  @Test(expected = NullInitialisationError.class)
  public void testBinaryWithNullSymbol() {
    Term t = new FunctionalTerm(null, constantTerm("a", baseType("b")),
                                      constantTerm("a", baseType("c")));
  }

  @Test(expected = NullInitialisationError.class)
  public void testFunctionalTermWithNullArgs() {
    FunctionSymbol f = new UserDefinedSymbol("f", arrowType("a", "b"));
    ArrayList<Term> args = null;
    Term t = new FunctionalTerm(f, args);
  }

  @Test(expected = ArityError.class)
  public void testFunctionalTermTooManyArgs() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new UserDefinedSymbol("f", type);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("b")));
    args.add(constantTerm("e", baseType("a")));
    Term t = new FunctionalTerm(f, args);
  }

  @Test(expected = TypingError.class)
  public void testConstructorBadArgType() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new UserDefinedSymbol("f", type);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("a")));
    Term t = new FunctionalTerm(f, args);
  }

  @Test(expected = IndexingError.class)
  public void testTooSmallSubterm() {
    Term t = twoArgTerm();
    Term x = t.queryImmediateSubterm(0);
  }

  @Test(expected = IndexingError.class)
  public void testTooLargeSubterm() {
    Term t = twoArgTerm();
    Term x = t.queryImmediateSubterm(3);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testInappropriateVariableRequest() {
    Term t = twoArgTerm();
    Term x = t.queryVariable();
  }

  @Test(expected = NullInitialisationError.class)
  public void testVariableNullName() {
    Variable x = new Var(null, baseType("o"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testVariableNullType() {
    Variable x = new Var("x", null);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testVariableRoot() {
    Variable x = new Var("x", baseType("o"));
    x.queryRoot();
  }

  @Test(expected = IndexingError.class)
  public void testVariableSubterm() {
    Variable x = new Var("x", baseType("o"));
    x.queryImmediateSubterm(1);
  }

  @Test
  public void testImmediateSubterms() {
    Term t = twoArgTerm();
    assertTrue(t.numberImmediateSubterms() == 2);
    assertTrue(t.queryImmediateSubterm(1).equals(constantTerm("c", baseType("a"))));
    assertTrue(t.queryImmediateSubterm(2).toString().equals("g(d)"));
  }

  @Test
  public void testFunctionalTermBasics() {
    Term t = twoArgTerm();
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    assertTrue(t.queryTermKind() == Term.TermKind.FUNCTIONALTERM);
    assertTrue(t.queryRoot().equals(new UserDefinedSymbol("f", type)));
    assertTrue(t.toString().equals("f(c, g(d))"));
  }

  @Test
  public void testFunctionalTermEquality() {
    Term s1 = constantTerm("x", baseType("o"));
    Term s2 = unaryTerm("x", baseType("o"), constantTerm("y", baseType("a")));
    Term s3 = unaryTerm("x", baseType("o"), constantTerm("y", baseType("a")));
    Term s4 = unaryTerm("x", baseType("a"), constantTerm("y", baseType("a")));
    assertFalse(s1.equals(s2));
    assertFalse(s2.equals(s1));
    assertTrue(s2.equals(s3));
    assertFalse(s2.equals(s4));
    assertFalse(s1.equals(new Var("x", baseType("o"))));
    assertTrue(s1.equals(new FunctionalTerm(new UserDefinedSymbol("x", baseType("o")),
                                            new ArrayList<Term>())));
  }

  @Test
  public void testVarTermBasics() {
    Variable x = new Var("x", baseType("o"));
    Term s = x;
    assertTrue(s.queryTermKind() == Term.TermKind.VARTERM);
    assertTrue(s.queryVariable().equals(x));
    assertTrue(s.toString().equals("x"));
    assertTrue(s.numberImmediateSubterms() == 0);
  }

  @Test
  public void testVarTermEquality() {
    Term s1 = new Var("x", baseType("o"));
    Term s2 = new Var("x", baseType("o"));
    assertTrue(s1.equals(s1));
    assertFalse(s1.equals(s2));
  }

  @Test
  public void testVarOrFunctionalTerm() {
    Term s1 = new Var("x", baseType("o"));
    Term s2 = constantTerm("x", baseType("o"));
    assertFalse(s1.equals(s2));
    assertFalse(s2.equals(s1));
    assertTrue(s1.toString().equals(s2.toString()));
  }
}
