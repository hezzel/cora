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
import cora.exceptions.ArityError;
import cora.exceptions.IndexingError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.NullCallError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;
import cora.terms.positions.*;

public class FunctionalTermTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  private Term constantTerm(String name, Type type) {
    return new UserDefinedSymbol(name, type);
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
  public void testNullArgs() {
    FunctionSymbol f = new UserDefinedSymbol("f", arrowType("a", "b"));
    ArrayList<Term> args = null;
    Term t = new FunctionalTerm(f, args);
  }

  @Test(expected = ArityError.class)
  public void testTooManyArgs() {
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

  @Test(expected = NullCallError.class)
  public void testNullMatch() {
    Term t = twoArgTerm();
    Substitution subst = new Subst();
    t.match(null, subst);
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
    assertTrue(t.isFunctionalTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isVarTerm());
    assertTrue(t.queryRoot().equals(new UserDefinedSymbol("f", type)));
    assertTrue(t.toString().equals("f(c, g(d))"));
  }

  @Test
  public void testConstantFunctionalTerm() {
    FunctionSymbol f = new UserDefinedSymbol("f", arrowType("b", "a"));
    ArrayList<Term> args = new ArrayList<Term>();
    Term fterm = new FunctionalTerm(f, args);
    assertTrue(fterm.isConstant());
  }

  @Test
  public void testTermEquality() {
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
  public void testVars() {
    // let's create: f(f(x,c),g(y,x))
    FunctionSymbol f = new UserDefinedSymbol("f", new ArrowType(baseType("a"),arrowType("b","a")));
    FunctionSymbol g = new UserDefinedSymbol("g", new ArrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new UserDefinedSymbol("c", baseType("b"));
    Variable x = new Var("x", baseType("a"));
    Variable y = new Var("y", baseType("b"));
    Term s = new FunctionalTerm(f, new FunctionalTerm(f, x, c), new FunctionalTerm(g, y, x));
    Environment env = s.vars();
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertTrue(env.size() == 2);
  }

  @Test
  public void testVarOrFunctionalTerm() {
    Term s1 = new Var("x", baseType("o"));
    Term s2 = constantTerm("x", baseType("o"));
    assertFalse(s2.equals(s1));
  }

  @Test
  public void testFirstOrder() {
    Type aa = arrowType("a", "a");
    Term s = twoArgTerm();
    Term t = unaryTerm("h", aa, new Var("x", baseType("b")));
    Type utype = new ArrowType(baseType("a"), new ArrowType(aa, baseType("b")));
    Term q = new FunctionalTerm(new UserDefinedSymbol("u", utype), s, t);
    assertTrue(s.queryFirstOrder());
    assertFalse(t.queryFirstOrder());
    assertFalse(q.queryFirstOrder());
  }

  @Test
  public void testPositions() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new UserDefinedSymbol("f", type);
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), new Var("x", baseType("b")));
    Term term = new FunctionalTerm(f, arg1, arg2);    // f(c,g(x))
    ArrayList<Position> lst = term.queryAllPositions();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).toString().equals("1.ε"));
    assertTrue(lst.get(1).toString().equals("2.1.ε"));
    assertTrue(lst.get(2).toString().equals("2.ε"));
    assertTrue(lst.get(3).toString().equals("ε"));
  }

  @Test
  public void testSubtermGood() {
    Position p;
    Term s = twoArgTerm();
    p = new EmptyPosition();
    assertTrue(s.querySubterm(p).equals(s));
    p = new ArgumentPosition(1, new EmptyPosition());
    assertTrue(s.querySubterm(p).equals(constantTerm("c", baseType("a"))));
    p = new ArgumentPosition(2, new ArgumentPosition(1, new EmptyPosition()));
    assertTrue(s.querySubterm(p).equals(constantTerm("d", baseType("b"))));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermBad() {
    Term s = twoArgTerm();
    Position pos = new ArgumentPosition(1, new ArgumentPosition(2, new EmptyPosition()));
    Term t = s.querySubterm(pos);
  }

  @Test
  public void testSubtermReplacementGood() {
    Term s = unaryTerm("f", baseType("Int"), constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(1, new EmptyPosition()), s);
    assertTrue(s.toString().equals("f(37)"));
    assertTrue(t.queryImmediateSubterm(1).equals(s));
    assertTrue(t.toString().equals("f(f(37))"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBad() {
    Term s = unaryTerm("f", baseType("o"), constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(2, new EmptyPosition()), s);
  }

  @Test(expected = ArityError.class)
  public void testApplyingBaseTerm() {
    Term s = twoArgTerm();
    Term t = constantTerm("37", baseType("Int"));
    s.apply(t);
  }

  @Test(expected = TypingError.class)
  public void testApplyingBadType() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = new ArrowType(a, new ArrowType(o, a));
    Term c = constantTerm("c", a); 
    FunctionSymbol f = new UserDefinedSymbol("f", type);
    Term fc = new FunctionalTerm(f, c); 
    fc.apply(c);
  }

  @Test
  public void testCorrectApplication() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = new ArrowType(a, new ArrowType(o, new ArrowType(a, o)));
    Term c = constantTerm("c", a); 
    FunctionSymbol f = new UserDefinedSymbol("f", type);
    Term fc = new FunctionalTerm(f, c); 
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(constantTerm("b", o));
    args.add(c);
    Term fcbc = fc.apply(args);
    assertTrue(fcbc.toString().equals("f(c, b, c)"));
  }

  @Test
  public void testSubstituting() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new Var("y", baseType("Int"));
    Type plustype = new ArrowType(baseType("Int"),new ArrowType(baseType("Int"), baseType("Int")));
    Type geqtype = new ArrowType(baseType("Int"),new ArrowType(baseType("Int"), baseType("Bool")));
    FunctionSymbol plus = new UserDefinedSymbol("plus", plustype);
    FunctionSymbol geq = new UserDefinedSymbol("geq", geqtype);
    Term addition = new FunctionalTerm(plus, x, constantTerm("42", baseType("Int")));
    Term comparison = new FunctionalTerm(geq, addition, y);
    // comparison = geq(plus(x, 42), y)

    Term thirtyseven = constantTerm("37", baseType("Int"));

    Substitution gamma = new Subst(x, thirtyseven);
    gamma.extend(y, x);

    Term additionsub = addition.substitute(gamma);
    assertTrue(additionsub.toString().equals("plus(37, 42)"));
    Term comparisonsub = comparison.substitute(gamma);
    assertTrue(comparisonsub.isFunctionalTerm());
    assertTrue(comparisonsub.numberImmediateSubterms() == 2);
    assertTrue(comparisonsub.queryImmediateSubterm(1).equals(additionsub));
    assertTrue(comparisonsub.queryImmediateSubterm(2).equals(x));
  }

  @Test
  public void testFirstOrderMatching() {
    Type ii = baseType("Int");
    Variable x = new Var("x", ii);
    Variable y = new Var("y", ii);
    Variable z = new Var("z", ii);
    Type ty = new ArrowType(ii, new ArrowType(ii, ii));
    FunctionSymbol plus = new UserDefinedSymbol("plus", ty);
    FunctionSymbol f = new UserDefinedSymbol("f", ty);

    Term pattern1 = new FunctionalTerm(f, x, new FunctionalTerm(plus, y, z));
    Term pattern2 = new FunctionalTerm(f, x, new FunctionalTerm(plus, y, x));
    Term pattern3 = new FunctionalTerm(f, x, new FunctionalTerm(plus, y, y));
    Term pattern4 = new FunctionalTerm(plus, x, new FunctionalTerm(f, y, z));

    Term a = new FunctionalTerm(f, constantTerm("37", ii), z);
    Term combi = new FunctionalTerm(f, a, new FunctionalTerm(plus, y, a));

    Substitution subst1 = new Subst();
    Substitution subst2 = new Subst();
    Substitution subst3 = new Subst();
    Substitution subst4 = new Subst();

    assertTrue(pattern1.match(combi, subst1) == null);
    assertTrue(pattern2.match(combi, subst2) == null);
    assertTrue(pattern3.match(combi, subst3) != null);
    assertTrue(pattern4.match(combi, subst4) != null);

    assertTrue(subst1.domain().size() == 3);
    assertTrue(subst1.get(x).equals(a));
    assertTrue(subst1.get(y).equals(y));
    assertTrue(subst1.get(z).equals(a));

    assertTrue(subst2.domain().size() == 2);
    assertTrue(subst2.get(x).equals(a));
    assertTrue(subst2.get(y).equals(y));
  }
}
