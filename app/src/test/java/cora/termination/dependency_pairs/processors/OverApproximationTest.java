/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

// WARNING: MOST OF THE TESTS IN THIS FILE HAVE BEEN DISABLED
// This is because they use the SMT solver, and we don't want to do loads of file access in unit
// tests.  If you make changes to the file, please uncomment for a bit to check that it didn't
// muck anything up. :)

package cora.termination.dependency_pairs.processors;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import cora.termination.dependency_pairs.DP;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import static org.junit.jupiter.api.Assertions.*;

import cora.types.*;
import cora.terms.*;
import cora.rewriting.*;
import cora.reader.CoraInputReader;

class OverApproximationTest {
  private Type type(String text) {
    return CoraInputReader.readType(text);
  }

  @Test
  public void testRename() {
//    // f(x, y) => g(x) | [y | x]
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.boolSort);
    Term left = TermFactory.createConstant("f", type("Int -> Bool -> unit")).apply(x).apply(y);
    Term right = TermFactory.createConstant("g", type("Int -> unit")).apply(x);
    List<Variable> vars = new ArrayList<>();
    vars.add(x);
    vars.add(y);
    DP dp = new DP(left, right, y, vars);
    DP dp2 = OverApproximation.rename(dp);
//    assertTrue(dp2.lhs().toString().equals("f(x, y)"));
//    assertTrue(dp2.rhs().toString().equals("g(x)"));
//    assertTrue(dp2.constraint().isVariable());
//    Variable y2 = dp2.constraint().queryVariable();
//    assertTrue(dp2.vars().size() == 1);
//    Variable x2 = dp2.vars().iterator().next();
//    assertTrue(x != x2);
//    assertTrue(y != y2);
//    assertTrue(dp2.lhs().vars().size() == 2);
//    assertTrue(dp2.lhs().vars().contains(x2));
//    assertTrue(dp2.lhs().vars().contains(y2));
//    assertTrue(dp2.rhs().vars().size() == 1);
//    assertTrue(dp2.rhs().vars().contains(x2));
  }

  private TRS testTrs() {
    return CoraInputReader.readTrsFromString(
      "defined :: Int -> Int -> Int\n" +
        "defined(x, y) -> x + y\n"
    );
  }

/*
  @Test
  public void testReduceVariableInConstraint() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(TheoryFactory.createValue(0));
    Term anticonstraint = TheoryFactory.equalSymbol.apply(x).apply(TheoryFactory.createValue(0));
    Term top = TheoryFactory.createValue(true);
    Term three = TheoryFactory.createValue(3);
    Term minthree = TheoryFactory.createValue(-3);
    Term sum = TermFactory.createApp(TheoryFactory.plusSymbol, TheoryFactory.createValue(1), three);
    Reducer reducer = new Reducer(testTrs());
    TreeSet<Variable> empty = new TreeSet<Variable>();
    TreeSet<Variable> hasx = new TreeSet<Variable>(); hasx.add(x);
    // we don't actually need to create real DPs; just making sure the rhs and lhs are right
    Reducer.MyDP dp1 = new Reducer.MyDP(x, x, constraint, hasx);
    assertTrue(reducer.mayReduce(dp1, dp1));
    Reducer.MyDP dp2 = new Reducer.MyDP(x, x, anticonstraint, hasx);
    assertFalse(reducer.mayReduce(dp1, dp2));
    Reducer.MyDP dp3 = new Reducer.MyDP(three, x, anticonstraint, hasx);
    assertTrue(reducer.mayReduce(dp1, dp3));
    Reducer.MyDP dp4 = new Reducer.MyDP(minthree, x, anticonstraint, hasx);
    assertFalse(reducer.mayReduce(dp1, dp4));
    Reducer.MyDP dp5 = new Reducer.MyDP(x, x, top, empty);
    assertTrue(reducer.mayReduce(dp1, dp5));
    Reducer.MyDP dp6 = new Reducer.MyDP(sum, x, top, empty);
    assertFalse(reducer.mayReduce(dp1, dp6));
  }

  @Test
  public void testReduceVariableInvars() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term constraint = TheoryFactory.greaterSymbol.apply(x).apply(TheoryFactory.createValue(0));
    Term top = TheoryFactory.createValue(true);
    Term value = TheoryFactory.createValue(-3);
    Term sum = TermFactory.createApp(TheoryFactory.plusSymbol, TheoryFactory.createValue(1), value);
    Term a = TermFactory.createConstant("a", type("Int"));
    TreeSet<Variable> xset = new TreeSet<Variable>();
    xset.add(x);
    Reducer reducer = new Reducer(testTrs());
    Reducer.MyDP dp1 = new Reducer.MyDP(x, x, top, xset);
    assertTrue(reducer.mayReduce(dp1, dp1));
    Reducer.MyDP dp2 = new Reducer.MyDP(x, x, constraint, xset);
    assertTrue(reducer.mayReduce(dp1, dp2));
    Reducer.MyDP dp3 = new Reducer.MyDP(x, x, top, new TreeSet<Variable>());
    assertTrue(reducer.mayReduce(dp1, dp3));
    Reducer.MyDP dp4 = new Reducer.MyDP(sum, x, top, new TreeSet<Variable>());
    assertTrue(reducer.mayReduce(dp1, dp4));
    Reducer.MyDP dp5 = new Reducer.MyDP(a, a, top, new TreeSet<Variable>());
    assertFalse(reducer.mayReduce(dp1, dp5));
  }

  @Test
  public void testReduceValue() {
    // 3 -> x mag, 3 -> 1 + 2 niet, 3 -> x [ x < 2] niet
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Term top = TheoryFactory.createValue(true);
    Term constraint = TheoryFactory.greaterSymbol.apply(TheoryFactory.createValue(2)).apply(x);
    Term three = TheoryFactory.createValue(3);
    Term sum = TheoryFactory.plusSymbol.apply(TheoryFactory.createValue(1))
                                       .apply(TheoryFactory.createValue(2));
    TreeSet<Variable> empty = new TreeSet<Variable>();
    TreeSet<Variable> xset = new TreeSet<Variable>(); xset.add(x);
    Reducer reducer = new Reducer(testTrs());
    Reducer.MyDP dp1 = new Reducer.MyDP(three, three, top, empty);
    assertTrue(reducer.mayReduce(dp1, dp1));
    Reducer.MyDP dp2 = new Reducer.MyDP(sum, three, top, xset);
    assertFalse(reducer.mayReduce(dp1, dp2));
    assertTrue(reducer.mayReduce(dp2, dp1));
    Reducer.MyDP dp3 = new Reducer.MyDP(x, x, constraint, xset);
    assertFalse(reducer.mayReduce(dp1, dp3));
  }

  private boolean checkReduce(Term from, Term fromConstraint, TreeSet<Variable> fromtheory,
                              Term to, Term toConstraint, TreeSet<Variable> totheory) {
    Reducer.MyDP dp1 = new Reducer.MyDP(from, from, fromConstraint, fromtheory);
    Reducer.MyDP dp2 = new Reducer.MyDP(to, to, toConstraint, totheory);
    Reducer reducer = new Reducer(testTrs());
    return reducer.mayReduce(dp1, dp2);
  }

  @Test
  public void testReduceTheoryTerm() {
    // [+](x) [x > 0] -> [+](2 + 3)
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    Term top = TheoryFactory.createValue(true);
    Term xis0 = TheoryFactory.equalSymbol.apply(x).apply(TheoryFactory.createValue(0));
    Term ysm0 = TheoryFactory.smallerSymbol.apply(y).apply(TheoryFactory.createValue(0));
    Term ygr0 = TheoryFactory.greaterSymbol.apply(y).apply(TheoryFactory.createValue(0));
    TreeSet<Variable> empty = new TreeSet<Variable>();
    TreeSet<Variable> xset = new TreeSet<Variable>(); xset.add(x);
    TreeSet<Variable> yset = new TreeSet<Variable>(); yset.add(y);
    Term one = TheoryFactory.createValue(1);
    Term two = TheoryFactory.createValue(2);
    Term thr = TheoryFactory.createValue(3);
    Term min = TheoryFactory.createValue(-3);
    Term xplus1 = TheoryFactory.plusSymbol.apply(x).apply(one);
    Term xtimesx = TheoryFactory.timesSymbol.apply(x).apply(x);
    Term xtimes1 = TheoryFactory.timesSymbol.apply(x).apply(one);
    Term xtimesy = TheoryFactory.timesSymbol.apply(x).apply(y);
    Term a = TermFactory.createConstant("a", type("Int"));
    Term twoplusthree = TheoryFactory.plusSymbol.apply(two).apply(thr);
    Term threetimestwo = TheoryFactory.timesSymbol.apply(thr).apply(two);

    assertFalse(checkReduce(xplus1, xis0, xset, two, top, empty)); // x + 1 [x = 0] -> 2
    assertTrue(checkReduce(xplus1, xis0, xset, one, top, empty));  // x + 1 [x = 0] -> 1
    assertFalse(checkReduce(xplus1, xis0, xset, y, ysm0, yset));   // x + 1 [x = 0] -> y [y < 0]
    assertTrue(checkReduce(xplus1, xis0, xset, y, ygr0, yset));    // x + 1 [x = 0] -> y [y > 0]
    assertTrue(checkReduce(xtimesx, top, empty, min, top, empty)); // x * x -> -3
    assertFalse(checkReduce(xtimesx, top, xset, min, top, empty)); // x * x [ | x ] -> -3
    assertFalse(checkReduce(xtimesx, top, empty, a, top, empty));  // x * x -> a
    assertFalse(checkReduce(xtimes1, top, empty, twoplusthree, top, empty));  // x * 1 -> 2 + 3
    assertFalse(checkReduce(xtimes1, top, xset, twoplusthree, top, empty));   // x * 1 [ | x ] -> 2 + 3
    assertTrue(checkReduce(xtimesy, top, xset, threetimestwo, top, empty));   // x * y -> 3 * 2
    assertFalse(checkReduce(xtimes1, top, xset, threetimestwo, top, empty));   // x * 1 -> 3 * 2
    assertFalse(checkReduce(TheoryFactory.plusSymbol.apply(y), ygr0, yset,  // [+](y) [y > 0] ->
                           TheoryFactory.plusSymbol.apply(twoplusthree),    //    [+](2+3)
                              top, empty));
    assertTrue(checkReduce(TheoryFactory.plusSymbol.apply(y), top, yset,   // [+](y) -> [+](2+3)
                           TheoryFactory.plusSymbol.apply(twoplusthree), top, empty));
  }

  @Test
  public void testConstructor() {
    Variable x = TheoryFactory.createVar("x", TypeFactory.intSort);
    Variable y = TheoryFactory.createVar("y", TypeFactory.intSort);
    FunctionSymbol c = TermFactory.createConstant("c", type("Int -> Int -> Int"));
    FunctionSymbol d = TermFactory.createConstant("d", type("Int -> Int -> Int"));
    FunctionSymbol a = TermFactory.createConstant("a", type("Int"));
    FunctionSymbol b = TermFactory.createConstant("b", type("Int"));
    Term one = TheoryFactory.createValue(1);
    Term two = TheoryFactory.createValue(2);
    Term thr = TheoryFactory.createValue(3);
    Term top = TheoryFactory.createValue(true);
    TreeSet<Variable> empty = new TreeSet<Variable>();
    TreeSet<Variable> xset = new TreeSet<Variable>(); xset.add(x);
    TreeSet<Variable> yset = new TreeSet<Variable>(); yset.add(y);
    Term cxx = c.apply(x).apply(x);
    Term cxy = c.apply(x).apply(y);
    Variable f = TermFactory.createVar("F", type("Int -> Int"));
    Variable g = TermFactory.createVar("F", type("Bool -> Int"));
    Term ygr0 = TheoryFactory.greaterSymbol.apply(y).apply(TheoryFactory.createValue(0));
    Term sum = TheoryFactory.plusSymbol.apply(one).apply(two);

    // c(a,x) -> c(x,b)
    assertTrue(checkReduce(c.apply(a).apply(x), top, empty, c.apply(x).apply(b), top, empty));
    // c(x,y) -> d(x,y)
    assertFalse(checkReduce(cxy, top, empty, d.apply(x).apply(y), top, empty));
    // c(x,x) -> c(2,3)
    assertTrue(checkReduce(cxx, top, empty, c.apply(two).apply(thr), top, empty));
    // c(x,x) [ | x] -> c(2,3)
    assertFalse(checkReduce(cxx, top, xset, c.apply(two).apply(thr), top, empty));
    // c(2,3) -> c(x,x)
    assertFalse(checkReduce(c.apply(two).apply(thr), top, empty, cxx, top, empty));
    // c(x,y) -> F(1+2)
    assertTrue(checkReduce(cxy, top, xset, f.apply(sum), top, empty));
    // c(x,y) [y > 0] -> F(1+2)
    assertFalse(checkReduce(cxy, ygr0, yset, f.apply(sum), top, empty));
    // c(x,y) -> G(true)
    assertFalse(checkReduce(cxy, top, empty, g.apply(TheoryFactory.createValue(true)), top, empty));
    // c(x) -> F(1)
    assertTrue(checkReduce(c.apply(x), top, empty, f.apply(one), top, empty));
    // c(y) [y > 0] -> F(-2)
    assertFalse(checkReduce(c.apply(y), ygr0, yset,
                            f.apply(TheoryFactory.createValue(-2)), top, empty));
  }

  @Test
  public void testRuleArity() {
    TRS trs = CoraInputReader.readTrsFromString(
      "id :: Int -> Int\n" +
      "f :: Int -> A -> Bool -> Int\n" +
      "a :: A\n" +
      "[+](f(x,y,z)) -> id\n" +
      "id(x) -> x\n" +
      "f(x,a) -> f(0,a)\n" +
      "f(0,a,false) -> 3\n"
    );
    FunctionSymbol id = trs.lookupSymbol("id");
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol a = trs.lookupSymbol("a");
    FunctionSymbol plus = TheoryFactory.plusSymbol;
    FunctionSymbol times = TheoryFactory.timesSymbol;
    Reducer reducer = new Reducer(trs);
    assertTrue(reducer.ruleArity(id) == 1);
    assertTrue(reducer.ruleArity(f) == 2);
    assertTrue(reducer.ruleArity(a) == 1);
    assertTrue(reducer.ruleArity(plus) == 1);
    assertTrue(reducer.ruleArity(times) == 3);
  }
*/
}
