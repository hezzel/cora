/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.reader;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import cora.exceptions.ParseError;
import cora.types.TypeFactory;
import cora.terms.Term;
import cora.terms.Variable;
import cora.terms.FunctionSymbol;
import cora.terms.TermFactory;
import cora.rewriting.TRS;

public class OCocoUnsortedInputReaderTest {
  @Test
  public void testReadSingleVariable() {
    Term term = OCocoUnsortedInputReader.readTerm("x", "x");
    assertTrue(term.isVariable());
    assertTrue(term.toString().equals("x"));
  }

  @Test
  public void testReadSingleConstant() {
    Term term = OCocoUnsortedInputReader.readTerm("x", "");
    assertTrue(term.isConstant());
    assertTrue(term.toString().equals("x"));
  }

  @Test
  public void testReadEmptyBracketList() {
    Term term = OCocoUnsortedInputReader.readTerm("x()", "");
    assertTrue(term.isConstant());
    assertTrue(term.toString().equals("x"));
  }

  @Test
  public void testReadSameSymbolTwice() {
    Term term = OCocoUnsortedInputReader.readTerm("f(f(x))", "x");
    assertTrue(term.toString().equals("f(f(x))"));
    assertTrue(term.queryRoot().equals(term.queryArgument(1).queryRoot()));
  }

  @Test
  public void testReadSameVariableTwice() {
    Term term = OCocoUnsortedInputReader.readTerm("f(x, x)", "x y");
    assertTrue(term.toString().equals("f(x, x)"));
    assertTrue(term.queryArgument(1) == term.queryArgument(2));
  }

  @Test
  public void testReadComplexTerm() {
    Term term = OCocoUnsortedInputReader.readTerm("f(g(x, y), h(x, u(), g(a, y)))",
                                                  "x y u v");
    assertTrue(term.toString().equals("f(g(x, y), h(x, u, g(a, y)))"));
    assertTrue(term.vars().size() == 3);
  }

  @Test
  public void testAbusedVariable() {
    try { OCocoUnsortedInputReader.readTerm("x(a)", "x"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals("1:1: Variable x used as root of a functional term.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testInconsistentArities() {
    try { OCocoUnsortedInputReader.readTerm("g(f(x, f(a)), a(y))", "x y"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:8: Function symbol f was previously used with 2 arguments, but is here used with 1.\n" +
        "1:15: Function symbol a was previously used with 0 arguments, but is here used with 1.\n"
      ));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void noTypingAttemptAfterParsingErrors() {
    try { OCocoUnsortedInputReader.readTerm("g(f(x y), f(x, y, z))", "x y z"); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:7: Expected a comma or closing bracket but got IDENTIFIER (y).\n"
      ));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadSimpleTrs() {
    TRS trs = OCocoUnsortedInputReader.readTrsFromString("(VAR x y)\n" +
                                                 "(RULES\n" +
                                                 "  +(x, 0) -> x\n" +
                                                 "  +(x, s(y)) -> s(+(x,y))\n" +
                                                 ")");
    assertTrue(trs.lookupSymbol("0").queryType().equals(TypeFactory.createSort("o")));
    assertTrue(trs.lookupSymbol("s").queryType().toString().equals("o ⇒ o"));
    assertTrue(trs.lookupSymbol("+").queryType().toString().equals("o ⇒ o ⇒ o"));
    assertTrue(trs.lookupSymbol("x") == null);
    assertTrue(trs.lookupSymbol("y") == null);
    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).toString().equals("+(x, 0) → x"));
    assertTrue(trs.queryRule(1).toString().equals("+(x, s(y)) → s(+(x, y))"));
    Variable x1 = trs.queryRule(0).queryLeftSide().queryArgument(1).queryVariable();
    Variable x2 = trs.queryRule(1).queryLeftSide().queryArgument(1).queryVariable();
    assertTrue(x1 != null && x2 != null && x1 != x2);
  }

  @Test
  public void testReadTrsWithSignatureAndComment() {
    String str = "(VAR x ys xs)\n" +
                 "(SIG (nil 0) (cons 2) (append 2) (0 0) (s 1))\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ") (COMMENT hello world!)";
    TRS trs = OCocoUnsortedInputReader.readTrsFromString(str);
    FunctionSymbol append = trs.lookupSymbol("append");
    FunctionSymbol cons = trs.lookupSymbol("cons");
    FunctionSymbol nil = trs.lookupSymbol("nil");
    FunctionSymbol zero = trs.lookupSymbol("0");
    FunctionSymbol suc = trs.lookupSymbol("s");
    Term s = TermFactory.createApp(cons, suc.apply(zero), nil);
    Term t = TermFactory.createApp(cons, zero, TermFactory.createApp(cons, zero, nil));
    Term q = TermFactory.createApp(append, s, t);
    assertTrue(q.toString().equals("append(cons(s(0), nil), cons(0, cons(0, nil)))"));
    q = trs.leftmostInnermostReduce(q);
    q = trs.leftmostInnermostReduce(q);
    assertTrue(q.toString().equals("cons(s(0), cons(0, cons(0, nil)))"));
    assertTrue(trs.leftmostInnermostReduce(q) == null);
  }

  @Test
  public void readTrsWithIncompleteSignature() {
    String str = "(VAR x ys xs)\n" +
                 "(SIG (nil 0) (cons 2) (0 0) (s 1))\n" +
                 "(RULES\n" +
                 "  append(nil, ys) -> ys\n" +
                 "  append(cons(x, xs), ys) -> cons(x, append(xs, ys))\n" +
                 ")";
    try { OCocoUnsortedInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "Undeclared function symbol (not allowed when SIG is given): append\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testSameNameForVarAndSymbol() {
    String str = "(VAR x f)\n" +
                 "(SIG (f 1) (g 2) (a 0))\n" +
                 "(RULES g(a) -> a)";
    try { OCocoUnsortedInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:8: Duplicate symbol: f occurs both as a variable and as a function symbol!\n"));
      // note that the arity error for g isn't even given anymore; this is so problematic that
      // type-checking is aborted
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testWrongKindOfTrs() {
    String str = "(SIG (f a -> a) (g b -> b)) (RULES f(x) -> x g(x) -> x)";
    try { OCocoUnsortedInputReader.readTrsFromString(str); }
    catch (ParseError e) {
      assertTrue(e.getMessage().equals(
        "1:7: Many-sorted function symbol f cannot occur in an unsorted TRS.\n" +
        "1:18: Many-sorted function symbol g cannot occur in an unsorted TRS.\n"));
      // note that the arity error for g isn't even given anymore; this is so problematic that
      // type-checking is aborted
      return;
    }
    assertTrue(false);
  }
}

