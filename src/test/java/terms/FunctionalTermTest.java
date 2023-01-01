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

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import java.util.List;
import cora.exceptions.*;
import cora.types.Type;

public class FunctionalTermTest extends TermTestFoundation {
  @Test(expected = NullInitialisationError.class)
  public void testUnaryWithNullArg() {
    FunctionSymbol f = new Constant("f", arrowType("a", "b"));
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
    FunctionSymbol f = new Constant("f", arrowType("a", "b"));
    List<Term> args = null;
    Term t = new FunctionalTerm(f, args);
  }

  @Test(expected = ArityError.class)
  public void testTooManyArgs() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new Constant("f", type);
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("b")));
    args.add(constantTerm("e", baseType("a")));
    Term t = new FunctionalTerm(f, args);
  }

  @Test(expected = TypingError.class)
  public void testConstructorBadArgType() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new Constant("f", type);
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("c", baseType("a")));
    args.add(constantTerm("d", baseType("a")));
    Term t = new FunctionalTerm(f, args);
  }

  @Test(expected = IndexingError.class)
  public void testTooSmallSubterm() {
    Term t = twoArgFuncTerm();
    Term x = t.queryArgument(0);
  }

  @Test(expected = IndexingError.class)
  public void testTooLargeSubterm() {
    Term t = twoArgFuncTerm();
    Term x = t.queryArgument(3);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testInappropriateVariableRequest() {
    Term t = twoArgFuncTerm();
    Term x = t.queryVariable();
  }

  @Test(expected = NullCallError.class)
  public void testNullMatch() {
    Term t = twoArgFuncTerm();
    Substitution subst = new Subst();
    t.match(null, subst);
  }

  @Test
  public void testArguments() {
    Term t = twoArgFuncTerm();
    assertTrue(t.numberArguments() == 2);
    assertTrue(t.queryArgument(1).equals(constantTerm("c", baseType("a"))));
    assertTrue(t.queryArgument(2).toString().equals("g(d)"));
    List<Term> args = t.queryArguments();
    assertTrue(args.get(0) == t.queryArgument(1));
    assertTrue(args.get(1) == t.queryArgument(2));
  }

  @Test
  public void testImmediateHeadSubterms() {
    Term t = twoArgFuncTerm();
    assertTrue(t.queryImmediateHeadSubterm(0).toString().equals("f"));
    assertTrue(t.queryImmediateHeadSubterm(1).toString().equals("f(c)"));
    assertTrue(t.queryImmediateHeadSubterm(2).toString().equals("f(c, g(d))"));
  }

  @Test
  public void testFunctionalTermBasics() {
    Term t = twoArgFuncTerm();
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    assertTrue(t.isFunctionalTerm());
    assertFalse(t.isConstant());
    assertFalse(t.isVariable());
    assertFalse(t.isVarTerm());
    assertTrue(t.isPattern());
    assertTrue(t.isApplication());
    assertTrue(t.queryRoot().equals(new Constant("f", type)));
    assertTrue(t.queryHead().equals(t.queryRoot()));
    assertTrue(t.toString().equals("f(c, g(d))"));
  }

  @Test
  public void testConstantFunctionalTerm() {
    FunctionSymbol f = new Constant("f", arrowType("b", "a"));
    List<Term> args = new ArrayList<Term>();
    Term fterm = new FunctionalTerm(f, args);
    assertTrue(fterm.isConstant());
    assertFalse(fterm.isApplication());
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
    assertFalse(s1.equals(new Var("x", baseType("o"), false)));
    assertTrue(s1.equals(new FunctionalTerm(new Constant("x", baseType("o")),
                                            new ArrayList<Term>())));
  }

  @Test
  public void testVars() {
    // let's create: f(f(x,c),g(y,x))
    FunctionSymbol f = new Constant("f", arrowType(baseType("a"),arrowType("b","a")));
    FunctionSymbol g = new Constant("g", arrowType(baseType("b"),arrowType("a","b")));
    FunctionSymbol c = new Constant("c", baseType("b"));
    Variable x = new Var("x", baseType("a"), false);
    Variable y = new Var("y", baseType("b"), true);
    Term s = new FunctionalTerm(f, new FunctionalTerm(f, x, c), new FunctionalTerm(g, y, x));
    Environment env = s.vars();
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertTrue(env.size() == 2);
    // with x a non-binder variable, the term is neither closed nor ground
    assertFalse(s.isGround());
    assertFalse(s.isClosed());
    // but if all variables are non-binder variables, the term is closed
    y = new Var("y", baseType("b"), false);
    s = new FunctionalTerm(f, new FunctionalTerm(f, x, c), new FunctionalTerm(g, y, x));
    assertFalse(s.isGround());
    assertTrue(s.isClosed());
    // and if there are no variables, the term is ground
    FunctionSymbol a = new Constant("a", baseType("a"));
    FunctionSymbol b = new Constant("b", baseType("b"));
    s = new FunctionalTerm(f, new FunctionalTerm(f, a, c), new FunctionalTerm(g, b, a));
    assertTrue(s.isGround());
    assertTrue(s.isClosed());
  }

  @Test
  public void testVarOrFunctionalTerm() {
    Term s1 = new Var("x", baseType("o"), false);
    Term s2 = constantTerm("x", baseType("o"));
    assertFalse(s2.equals(s1));
  }

  @Test
  public void testFirstOrder() {
    Type aa = arrowType("a", "a");
    Term s = twoArgFuncTerm();
    Term t = unaryTerm("h", aa, new Var("x", baseType("b"), false));
    Type utype = arrowType(baseType("a"), arrowType(aa, baseType("b")));
    Term q = new FunctionalTerm(new Constant("u", utype), s, t);
    assertTrue(s.isFirstOrder());
    assertFalse(t.isFirstOrder());
    assertFalse(q.isFirstOrder());
  }

  @Test
  public void testNonPattern() {
    Var x = new Var("x", arrowType("A", "B"), false);
    Term xa = new VarTerm(x, constantTerm("a", baseType("A")));
    FunctionSymbol f = new Constant("f", arrowType("B", "B"));
    Term fxa = new FunctionalTerm(f, xa);
    assertFalse(fxa.isPattern());
  }

  @Test
  public void testPositions() {
    Type type = arrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new Constant("f", type);
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), new Var("x", baseType("b"), true));
    Term term = new FunctionalTerm(f, arg1, arg2);    // f(c,g(x))
    List<Position> lst = term.queryAllPositions();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).toString().equals("1.ε"));
    assertTrue(lst.get(1).toString().equals("2.1.ε"));
    assertTrue(lst.get(2).toString().equals("2.ε"));
    assertTrue(lst.get(3).toString().equals("ε"));
  }

  @Test
  public void testSubtermGood() {
    Position p;
    Term s = twoArgFuncTerm();
    p = PositionFactory.empty;
    assertTrue(s.querySubterm(p).equals(s));
    p = PositionFactory.createArg(1, PositionFactory.empty);
    assertTrue(s.querySubterm(p).equals(constantTerm("c", baseType("a"))));
    p = PositionFactory.createArg(2, PositionFactory.createArg(1, PositionFactory.empty));
    assertTrue(s.querySubterm(p).equals(constantTerm("d", baseType("b"))));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermBad() {
    Term s = twoArgFuncTerm();
    Position pos = PositionFactory.createArg(1, PositionFactory.createArg(2, PositionFactory.empty));
    Term t = s.querySubterm(pos);
  }

  @Test
  public void testSubtermReplacementGood() {
    Term s = unaryTerm("f", baseType("Int"), constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.createArg(1, PositionFactory.empty), s);
    assertTrue(s.toString().equals("f(37)"));
    assertTrue(t.queryArgument(1).equals(s));
    assertTrue(t.toString().equals("f(f(37))"));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermReplacementBad() {
    Term s = unaryTerm("f", baseType("o"), constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(PositionFactory.createArg(2, PositionFactory.empty), s);
  }

  @Test(expected = ArityError.class)
  public void testApplyingBaseTerm() {
    Term s = twoArgFuncTerm();
    Term t = constantTerm("37", baseType("Int"));
    s.apply(t);
  }

  @Test(expected = TypingError.class)
  public void testApplyingBadType() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = arrowType(a, arrowType(o, a));
    Term c = constantTerm("c", a); 
    FunctionSymbol f = new Constant("f", type);
    Term fc = new FunctionalTerm(f, c); 
    fc.apply(c);
  }

  @Test
  public void testCorrectApplication() {
    Type o = baseType("o");
    Type a = baseType("a");
    Type type = arrowType(a, arrowType(o, arrowType(a, o)));
    Term c = constantTerm("c", a); 
    FunctionSymbol f = new Constant("f", type);
    Term fc = new FunctionalTerm(f, c); 
    List<Term> args = new ArrayList<Term>();
    args.add(constantTerm("b", o));
    args.add(c);
    Term fcbc = fc.apply(args);
    assertTrue(fcbc.toString().equals("f(c, b, c)"));
  }

  @Test
  public void testSubstituting() {
    Variable x = new Var("x", baseType("Int"), false);
    Variable y = new Var("y", baseType("Int"), true);
    Type plustype = arrowType(baseType("Int"),arrowType(baseType("Int"), baseType("Int")));
    Type geqtype = arrowType(baseType("Int"),arrowType(baseType("Int"), baseType("Bool")));
    FunctionSymbol plus = new Constant("plus", plustype);
    FunctionSymbol geq = new Constant("geq", geqtype);
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
    assertTrue(comparisonsub.numberArguments() == 2);
    assertTrue(comparisonsub.queryArgument(1).equals(additionsub));
    assertTrue(comparisonsub.queryArgument(2).equals(x));
  }

  @Test
  public void testFirstOrderMatching() {
    Type ii = baseType("Int");
    Variable x = new Var("x", ii, false);
    Variable y = new Var("y", ii, false);
    Variable z = new Var("z", ii, true);
    Type ty = arrowType(ii, arrowType(ii, ii));
    FunctionSymbol plus = new Constant("plus", ty);
    FunctionSymbol f = new Constant("f", ty);

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
