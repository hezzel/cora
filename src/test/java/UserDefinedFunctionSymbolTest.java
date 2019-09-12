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
import java.lang.Error;
import java.util.ArrayList;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.IndexingError;
import cora.exceptions.NullInitialisationError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.types.*;
import cora.terms.positions.EmptyPosition;
import cora.terms.positions.ArgumentPosition;
import cora.terms.UserDefinedSymbol;
import cora.terms.Var;
import cora.terms.FunctionalTerm;
import cora.terms.Subst;

public class UserDefinedFunctionSymbolTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  @Test(expected = NullInitialisationError.class)
  public void testUserDefinedSymbolNullName() {
    FunctionSymbol f = new UserDefinedSymbol(null, baseType("o"));
  }

  @Test(expected = java.lang.Error.class)
  public void testUserDefinedSymbolEmptyName() {
    FunctionSymbol f = new UserDefinedSymbol("", baseType("o"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testUserDefinedSymbolNullType() {
    FunctionSymbol f = new UserDefinedSymbol("bing", null);
  }

  @Test
  public void testFunctionSymbolBasics() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    FunctionSymbol f = new UserDefinedSymbol("ff", combi);
    assertTrue(f.queryName().equals("ff"));
    assertTrue(f.toString().equals("ff"));
    assertTrue(f.queryType().equals(combi));
  }

  @Test
  public void testFunctionSymbolEquality() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    FunctionSymbol f = new UserDefinedSymbol("ff", combi);
    FunctionSymbol g = new UserDefinedSymbol("ff", combi);
    FunctionSymbol h = new UserDefinedSymbol("f", combi);
    FunctionSymbol i = new UserDefinedSymbol("f", new ArrowType(a,c));

    assertTrue(f.equals(g));
    assertFalse(f.equals(h));
    assertFalse(f.equals(i));
    assertFalse(f.equals(null));
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testVariableRequest() {
    Term f = new UserDefinedSymbol("f", baseType("a"));
    Term x = f.queryVariable();
  }

  @Test(expected = IndexingError.class)
  public void testBadPositionRequest() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = new ArrowType(a, b);
    UserDefinedSymbol f = new UserDefinedSymbol("f", combi);
    Term tmp = f.querySubterm(new ArgumentPosition(1, new EmptyPosition()));
  }

  @Test(expected = IndexingError.class)
  public void testBadPositionReplacement() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = new ArrowType(a, b);
    UserDefinedSymbol f = new UserDefinedSymbol("f", combi);
    Term tmp = f.replaceSubterm(new ArgumentPosition(1, new EmptyPosition()),
                                new UserDefinedSymbol("a", a));
  }

  @Test
  public void testTermBasics() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    Term f = new UserDefinedSymbol("ff", combi);
    Var x = new Var("ff", combi);

    assertTrue(f.queryType().equals(combi));
    assertTrue(f.isConstant());
    assertTrue(f.isFunctionalTerm());
    assertFalse(f.isVariable());
    assertFalse(f.isVarTerm());
    assertTrue(f.numberImmediateSubterms() == 0);
    assertTrue(f.queryRoot().equals(f));
    assertTrue(f.queryAllPositions().size() == 1);
    assertTrue(f.queryAllPositions().get(0).isEmpty());
    assertTrue(f.querySubterm(new EmptyPosition()).equals(f));
    assertTrue(f.replaceSubterm(new EmptyPosition(), x).equals(x));
    Subst gamma = new Subst(x, new UserDefinedSymbol("gg", combi));
    assertTrue(f.substitute(gamma).equals(f));
    assertTrue(f.vars().size() == 0);
    assertFalse(f.queryFirstOrder());
    Term aa = new UserDefinedSymbol("g", a);
    assertTrue(aa.queryFirstOrder());
  }

  @Test
  public void testTermEquality() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = new ArrowType(a, b);
    UserDefinedSymbol f = new UserDefinedSymbol("f", combi);
    UserDefinedSymbol g = new UserDefinedSymbol("f", combi);
    UserDefinedSymbol h = new UserDefinedSymbol("h", combi);

    assertTrue(f.equals((Term)f));
    assertTrue(f.equals((Term)g));
    assertFalse(f.equals((Term)h));

    ArrayList<Term> args = new ArrayList<Term>();
    Term ff = new FunctionalTerm(f, args);
    Term gg = new FunctionalTerm(g, args);
    args.add(new UserDefinedSymbol("aa", a));
    Term fa = new FunctionalTerm(f, args);

    assertTrue(f.equals(ff));
    assertTrue(f.equals(gg));
    assertFalse(f.equals(a));

    assertTrue(f.match(ff) != null);
  }
}
