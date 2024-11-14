/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.reader;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.exceptions.ParseException;
import charlie.types.TypeFactory;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;
import charlie.trs.Rule;
import charlie.trs.TRS;

public class OCocoSortedInputReaderTest {
  @Test
  public void testReadSingleVariable() {
    Term term = OCocoSortedInputReader.readTerm("x", "", TypeFactory.createSort("u"));
    assertTrue(term.isVariable());
    assertTrue(term.toString().equals("x"));
    assertTrue(term.queryType().toString().equals("u"));
  }

  @Test
  public void testReadSingleConstant() {
    Term term = OCocoSortedInputReader.readTerm("x", "(x -> a)");
    assertTrue(term.isConstant());
    assertTrue(term.toString().equals("x"));
    assertTrue(term.queryType().toString().equals("a"));
  }

  @Test
  public void testGuessType() {
    Term term = OCocoSortedInputReader.readTerm("x", "");
    assertTrue(term.isVariable());
    assertTrue(term.toString().equals("x"));
    assertTrue(term.queryType().toString().equals("o"));
  }

  @Test
  public void testReadSimpleCorrectTerm() {
    String sig = "(f B A -> C) (g A A -> B) (a -> A)";
    Term t = OCocoSortedInputReader.readTerm("f(g(x, y), a)", sig);
    FunctionSymbol f = t.queryRoot();
    FunctionSymbol g = t.queryArgument(1).queryRoot();
    FunctionSymbol a = t.queryArgument(2).queryRoot();
    Variable x = t.queryArgument(1).queryArgument(1).queryVariable();
    Variable y = t.queryArgument(1).queryArgument(2).queryVariable();
    Term combi = TermFactory.createApp(f, TermFactory.createApp(g, x, y), a);
    assertTrue(t.equals(combi));
  }

  @Test
  public void testReadTermWithSameVariableTwice() {
    String sig = "(f B B -> A) (g A A -> B)";
    Term t = OCocoSortedInputReader.readTerm("f(g(x,y),g(x,a))", sig);
    assertTrue(t.toString().equals("f(g(x, y), g(x, a))"));
    assertTrue(t.queryArgument(1).queryArgument(1) == t.queryArgument(2).queryArgument(1));
  }

  @Test
  public void testVariableUsedAsFunction() {
    try { OCocoSortedInputReader.readTerm("f(x, x(a))", "(a 1) (f 2)"); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:6: Variable x used as a function symbol!\n" +
        "1:8: Illegal occurrence of unapplied function symbol a!\n"
      ));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testUndeclaredUsedAsFunction() {
    try { OCocoSortedInputReader.readTerm("f(y, x(a))", "(a 1) (f 2)"); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:6: Undeclared function symbol: x.\n" +
        "1:8: Illegal occurrence of unapplied function symbol a!\n"
      ));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadTermWithSortErrors() {
    String sig = "(f A B -> C) (g A B -> A) (a -> B)";
    try { OCocoSortedInputReader.readTerm("f(g(x, y), g(a, g(a, x)))", sig); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:12: Expected term of type B, but got functional term g(...) of type A.\n" +
        "1:14: Expected term of type A, but got constant symbol a of type B.\n" +
        "1:17: Expected term of type B, but got functional term g(...) of type A.\n" +
        "1:19: Expected term of type A, but got constant symbol a of type B.\n" +
        "1:22: Expected term of type B, but got variable x that was previously used with type A.\n"
      ));
    }
  }

  @Test
  public void testReadTermWithArityErrors() {
    String sig = "(f A B -> C) (g A A -> A) (a -> B)";
    try { OCocoSortedInputReader.readTerm("f(g(x), z, g(x, a))", sig); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:1: Function symbol f was declared with 2 arguments, but is used here with 3.\n" +
        "1:3: Function symbol g was declared with 2 arguments, but is used here with 1.\n" +
        "1:17: Expected term of type A, but got constant symbol a of type B.\n"
      ));
    }
  }

  @Test
  public void readSameUndeclaredSymbolTwice() {
    String sig = "(f A A -> B) (a -> A)";
    try { OCocoSortedInputReader.readTerm("f(g(a), g(x))", sig); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:3: Undeclared function symbol: g.\n" +
        "1:9: Undeclared function symbol: g.\n"
      ));
    }
  }

  @Test
  public void testReadTermGivenTRS() {
    String str = "(VAR x ys xs)\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = OCocoUnsortedInputReader.readTrsFromString(str);
    Term t = OCocoSortedInputReader.readTerm("append(cons(x, nil), lst)", trs);
    assertTrue(t.vars().size() == 2);
  }

  @Test
  public void testReadTermTooMuch() {
    String str = "(VAR x ys xs)\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    TRS trs = OCocoUnsortedInputReader.readTrsFromString(str);
    try { OCocoSortedInputReader.readTerm("append(cons(x, nil), lst) xx", trs); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:27: Expected end of input but got IDENTIFIER (xx).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadSingleSortedRule() {
    String str = "(SIG (+ int int -> int) (s int -> int)) (RULES +(x, s ( y)) -> s(+(y,x)))";
    TRS trs = OCocoSortedInputReader.readTrsFromString(str);
    assertTrue(trs.queryRuleCount() == 1);
    assertTrue(trs.queryRule(0).toString().equals("+(x, s(y)) → s(+(y, x))"));
    assertTrue(trs.queryRule(0).queryRightSide().vars().size() == 2);
  }

  @Test
  public void testReadRuleWhereVariableHasDifferentTypesInDifferentRules() {
    String str = "(SIG (f Int -> Int) (g Bool -> Bool)) (RULES f(x) -> x g(x) -> x)";
    TRS trs = OCocoSortedInputReader.readTrsFromString(str);
    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).queryRightSide().queryVariable() !=
               trs.queryRule(1).queryRightSide().queryVariable());
  }

  @Test
  public void testReadRulesWhereSomeSymbolIsUndeclared() {
    String str = "(SIG (f 2) (0 0)) (RULES \n" +
      "  f(x,s(y)) -> f(s(x),y)\n" +
      "  f(x,0) -> g(x)" +
      ")";
    try { OCocoSortedInputReader.readTrsFromString(str); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
      "2:7: Undeclared function symbol: s.\n" +
      "2:18: Undeclared function symbol: s.\n" +
      "2:13: The rule f(x, s(y__1)) → f(s(x), y__2) is not allowed to occur in MSTRSs: " +
        "right-hand side contains a variable that does not occur in the left-hand side.\n" +
      "3:13: Undeclared function symbol: g.\n"));
        // the third error is given because the variable below s is not recognised as the same
        // variable; this does not cause a problem in the last case, because then x is already
        // known when it occurs in a type-mysterious place
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadRuleWhereLeftHasStructureProblems() {
    String str = "(SIG (f 2) (0 0)) (RULES\n" +
      "  f(x, s(y) -> f(g(x),y)\n" +
      "  f(x,0) -> g(x))";
    try { OCocoSortedInputReader.readTrsFromString(str); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "2:13: Expected a comma or closing bracket but got ARROW (->).\n" +
        "3:13: Undeclared function symbol: g.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadRuleWhereRightHasStructureProblems() {
    String str = "(SIG (f 2)) (RULES\n" +
      "  f(x, s(y)) -> f(g(x),,y)\n" +
      "  f(x) -> f(x, x))";
    try { OCocoSortedInputReader.readTrsFromString(str); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "2:24: Expected an identifier (variable or function name) but got COMMA (,).\n" +
        "2:8: Undeclared function symbol: s.\n" +
        "3:3: Function symbol f was declared with 2 arguments, but is used here with 1.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testRuleWithInconsistentTermTyping() {
    String str = "(SIG (f int -> bool) (g int -> int)) (RULES f(x) -> g(x))";
    try { OCocoSortedInputReader.readTrsFromString(str); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:53: Expected term of type bool, but got functional term g(...) of type int.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testRuleWithInconsistentVariableTyping() {
    String str = "(SIG (f Int -> Int) (g Bool -> Int)) (RULES f(x) -> g(x))";
    try { OCocoSortedInputReader.readTrsFromString(str); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:55: Expected term of type Bool, but got variable x that was previously used with " +
        "type Int.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testRuleWithFreshVariableOnRightSide() {
    String str = "(SIG (f 2) ) (RULES f(x,y) -> f(y,z))";
    try { OCocoSortedInputReader.readTrsFromString(str); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:28: The rule f(x, y) → f(y, z) is not allowed to occur in MSTRSs: right-hand side " +
        "contains a variable that does not occur in the left-hand side.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testRuleWithLeftVariable() {
    String str = "(SIG (f 2) ) (RULES x -> f(x,x))";
    try { OCocoSortedInputReader.readTrsFromString(str); }
    catch (ParseException e) {
      assertTrue(e.getMessage().equals(
        "1:23: The left-hand side of a rule is not allowed to be a variable.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadFullTrs() {
    String str = "(SIG " +
                 "  (app   List List -> List)" +
                 "  (cons  Nat List -> List)" +
                 "  (nil   -> List)" +
                 "  (s     Nat -> Nat)" +
                 "  (0     -> Nat)" +
                 "  (len   List -> Nat)" +
                 ")(RULES" +
                 "  app(nil,ys) -> ys" +
                 "  app(cons(x,xs),ys) -> cons(x,app(xs,ys))" +
                 "  len(nil) -> 0" +
                 "  len(cons(x, xs)) -> s(len(xs))" +
                 ") (COMMENT this is :) a comment) ";
    TRS trs = OCocoSortedInputReader.readTrsFromString(str);
    FunctionSymbol app = trs.lookupSymbol("app");
    assertTrue(app.queryType().toString().equals("List → List → List"));
    assertTrue(trs.queryRuleCount() == 4);
    Rule appbase = trs.queryRule(0);
    Rule lenadvanced = trs.queryRule(3);
    assertTrue(appbase.toString().equals("app(nil, ys) → ys"));
    assertTrue(lenadvanced.toString().equals("len(cons(x, xs)) → s(len(xs))"));
    Term left = lenadvanced.queryLeftSide();
    assertTrue(left.queryType().equals(TypeFactory.createSort("Nat")));
    assertTrue(left.queryArgument(1).queryType().equals(TypeFactory.createSort("List")));
  }
}

