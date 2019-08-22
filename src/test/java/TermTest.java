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

  @Test(expected = NullCallError.class)
  public void testNullSubstitution() {
    Term t = new Var("x", baseType("Int"));
    t.substitute(null);
  }

  @Test(expected = NullCallError.class)
  public void testNullMatchVar1() {
    Term t = new Var("x", baseType("Int"));
    t.match(constantTerm("37", baseType("Int")), null);
  }

  @Test(expected = NullCallError.class)
  public void testNullMatchVar2() {
    Term t = new Var("x", baseType("Int"));
    Substitution subst = new Subst();
    t.match(null, subst);
  }

  @Test(expected = NullCallError.class)
  public void testNullMatchFunctional() {
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

  @Test
  public void testVarPositions() {
    Term s = new Var("x", baseType("o"));
    ArrayList<Position> lst = s.queryAllPositions();
    assertTrue(lst.size() == 1);
    assertTrue(lst.get(0).toString().equals("ε"));
  }

  @Test
  public void testFunctionalTermPositions() {
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
  public void testVarSubtermGood() {
    Term s = new Var("x", baseType("o"));
    Position p = new EmptyPosition();
    assertTrue(s.querySubterm(p).equals(s));
  }

  @Test(expected = IndexingError.class)
  public void testVarSubtermBad() {
    Term s = new Var("x", baseType("o"));
    Position p = new ArgumentPosition(1, new EmptyPosition());
    Term t = s.querySubterm(p);
  }

  @Test
  public void testVarSubtermReplacementGood() {
    Term s = new Var("x", baseType("a"));
    Term t = twoArgTerm();
    Position p = new EmptyPosition();
    assertTrue(s.replaceSubterm(p, t).equals(t));
    assertTrue(s.toString().equals("x"));
  }

  @Test(expected = IndexingError.class)
  public void testVarSubtermReplacementBad() {
    Term s = new Var("x", baseType("o"));
    Position p = new ArgumentPosition(1, new EmptyPosition());
    Term t = s.replaceSubterm(p, twoArgTerm());
  }

  @Test
  public void testFunctionalTermSubtermGood() {
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
  public void testFunctionalTermSubtermBad() {
    Term s = twoArgTerm();
    Position pos = new ArgumentPosition(1, new ArgumentPosition(2, new EmptyPosition()));
    Term t = s.querySubterm(pos);
  }

  @Test
  public void testFunctionalTermSubtermReplacementGood() {
    Term s = unaryTerm("f", baseType("o"), constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(1, new EmptyPosition()), s);
    assertTrue(s.toString().equals("f(37)"));
    assertTrue(t.queryImmediateSubterm(1).equals(s));
    assertTrue(t.toString().equals("f(f(37))"));
  }

  @Test(expected = IndexingError.class)
  public void testFunctionalTermSubtermReplacementBad() {
    Term s = unaryTerm("f", baseType("o"), constantTerm("37", baseType("Int")));
    Term t = s.replaceSubterm(new ArgumentPosition(2, new EmptyPosition()), s);
  }

  @Test
  public void testSubstituteVar() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new Var("y", baseType("Int"));
    Variable z = new Var("z", baseType("Bool"));
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.extend(y, x); 
    assertTrue(x.substitute(gamma).equals(xterm));
    assertTrue(y.substitute(gamma).equals(x));
    assertTrue(z.substitute(gamma).equals(z));
  }

  @Test
  public void testSubstituteFunctional() {
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
    assertTrue(comparisonsub.queryTermKind() == Term.TermKind.FUNCTIONALTERM);
    assertTrue(comparisonsub.numberImmediateSubterms() == 2);
    assertTrue(comparisonsub.queryImmediateSubterm(1).equals(additionsub));
    assertTrue(comparisonsub.queryImmediateSubterm(2).equals(x));
  }

  @Test
  public void testVarMatchingNoMapping() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgTerm();
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testVarMatchingExistingMapping() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgTerm();
    Subst gamma = new Subst(x, t);
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testVarMatchingConflictingMapping() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgTerm();
    Term q = new Var("y", baseType("a"));
    Subst gamma = new Subst(x, q);
    assertTrue(x.match(t, gamma) != null);
    assertTrue(gamma.get(x).equals(q));
    assertTrue(gamma.domain().size() == 1);
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
