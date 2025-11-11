/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.termination.reduction_pairs.horpo;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.Set;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.smt.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import charlie.reader.CoraInputReader;
import cora.config.Settings;
import cora.termination.reduction_pairs.ArgumentFilter;
import cora.termination.reduction_pairs.horpo.HorpoConstraintList.HRelation;

public class HorpoSimplifierTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt, TrsFactory.LCSTRS);
  }

  private Type type(String txt) {
    return CoraInputReader.readType(txt);
  }

  private HorpoConstraintList makeList(TRS trs, SmtProblem smt) {
    return new HorpoConstraintList(new TermPrinter(trs.queryFunctionSymbolNames()), smt);
  }

  /**
   * This sets up a simplification problem l <relation> r | phi { x1,...,xn,y }, where l and r have
   * the given types and x1,...,xn are the variables of phi.  Then, it does a single simplification
   * step.
   * Both the resulting list and the corresponding state of the SmtProblem are returned.
   */
  private Pair<HorpoConstraintList,SmtProblem> setupSimplify(String l, String lsort, String r,
                 String rsort, String ysort, String phi, HRelation relation, String trsstring) {
    SmtProblem smt = new SmtProblem();
    TRS trs = makeTrs("Q :: (" + lsort + ") -> (" + rsort + ") -> (" + ysort + ") -> Bool -> unit"
                      + "\n" + trsstring);
    HorpoConstraintList lst = makeList(trs, smt);
    ArgumentFilter filter = new ArgumentFilter(smt);
    TreeSet<FunctionSymbol> funcs = new TreeSet<FunctionSymbol>(trs.queryAlphabet().getSymbols());
    HorpoParameters param = new HorpoParameters(1000, funcs, filter, smt);
    HorpoSimplifier simplifier = new HorpoSimplifier(param, lst, filter);
    Term term = CoraInputReader.readTerm("Q(" + l + ", " + r + ", y, " + phi + ")", trs);
    Term left = term.queryArgument(1);
    Term right = term.queryArgument(2);
    Term constraint = term.queryArgument(4);
    Variable y = term.queryArgument(3).queryVariable();
    TreeSet<Variable> tvar = new TreeSet<Variable>();
    tvar.add(y);
    for (Variable x : constraint.vars()) tvar.add(x);
    lst.store(left, relation, right, constraint, tvar);
    smt.clear();
    simplifier.simplify(lst.get(0));
    return new Pair<HorpoConstraintList,SmtProblem>(lst, smt);
  }

  /**
   * This sets up a simplification problem of the form f(x, d(y)) REL g(x, x) | x > 0 { x },
   * and does a single simplification step.  Here, REL is the given relation.
   * Both the resulting list and the corresponding state of the SmtPorblem are returned.
   */
  private Pair<HorpoConstraintList,SmtProblem> setupSimplify(HRelation relation) {
    return setupSimplify("f(x, d(y))", "Int", "g(x,x)", "Int", "Int", "y > 0", relation,
                         "f :: Int -> Int -> Int g :: Int -> Int -> Int d :: Int -> Int");
  }

  /**
   * This sets up a simplification problem of the form x+3 REL x+1 | x > 0 { x },
   * and does a single simplification step.  Here, REL is the given relation.
   * Both the resulting list and the corresponding state of the SmtPorblem are returned.
   */
  private Pair<HorpoConstraintList,SmtProblem> setupTheorySimplify(HRelation relation) {
    return setupSimplify("x+3", "Int", "x+1", "Int", "Int", "x > 0", relation, "");
  }

  private Pair<HorpoConstraintList,SmtProblem> setupVarSimplify(HRelation relation) {
    SmtProblem smt = new SmtProblem();
    TRS trs = makeTrs("Q :: A -> A\na :: A\nb :: A\nc :: Int -> A" +
                      "{ F :: A -> A -> A } Q(F(c(x), a)) -> Q(F(b, c(x))) | x = 0");
    HorpoConstraintList lst = makeList(trs, smt);
    ArgumentFilter filter = new ArgumentFilter(smt);
    TreeSet<FunctionSymbol> funcs = new TreeSet<FunctionSymbol>(trs.queryAlphabet().getSymbols());
    HorpoParameters param = new HorpoParameters(1000, funcs, filter, smt);
    HorpoSimplifier simplifier = new HorpoSimplifier(param, lst, filter);
    Term left = trs.queryRule(0).queryLeftSide().queryArgument(1);
    Term right = trs.queryRule(0).queryRightSide().queryArgument(1);
    Term constraint = trs.queryRule(0).queryConstraint();
    TreeSet<Variable> tvar = new TreeSet<Variable>();
    for (Variable x : constraint.vars()) tvar.add(x);
    lst.store(left, relation, right, constraint, tvar);
    smt.clear();
    simplifier.simplify(lst.get(0));
    return new Pair<HorpoConstraintList,SmtProblem>(lst, smt);
  }


  @Test
  public void testSimplifyGreater() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify(HRelation.GREATER);
    assertTrue(pair.fst().toString().equals(
      "[f(x, d(y)) ≻ g(x, x) | y > 0 { y }]\n" +
      "[f(x, d(y)) ≻{rpo} g(x, x) | y > 0 { y }]\n" +
      "[f(x, d(y)) ≻{var} g(x, x) | y > 0 { y }]\n" +
      "[f(x, d(y)) ≻{fun} g(x, x) | y > 0 { y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "![f(x, d(y)) ≻ g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≻{rpo} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≻{var} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≻{fun} g(x, x) | y > 0 { y }]\n"));
    pair = setupTheorySimplify(HRelation.GREATER);
    assertTrue(pair.fst().toString().equals(
      "[x + 3 ≻ x + 1 | x > 0 { x }]\n" +
      "[x + 3 ≻{theory} x + 1 | x > 0 { x }]\n"));
    assertTrue(pair.snd().toString().equals(
      "![x + 3 ≻ x + 1 | x > 0 { x }] or " +
      "[x + 3 ≻{theory} x + 1 | x > 0 { x }]\n"));
    pair = setupSimplify("x + 1", "Int", "x + 1", "Int", "Int", "y > 0", HRelation.GREATER, "");
    assertTrue(pair.fst().toString().equals("[x + 1 ≻ x + 1 | y > 0 { }]\n"));
    assertTrue(pair.snd().toString().equals("![x + 1 ≻ x + 1 | y > 0 { }]\n"));
  }

  @Test
  public void testSimplifyGeq() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify(HRelation.GEQ);
    assertTrue(pair.fst().toString().equals(
      "[f(x, d(y)) ≽ g(x, x) | y > 0 { y }]\n" +
      "[f(x, d(y)) ≻{rpo} g(x, x) | y > 0 { y }]\n" +
      "[f(x, d(y)) ≽{var} g(x, x) | y > 0 { y }]\n" +
      "[f(x, d(y)) ≽{fun} g(x, x) | y > 0 { y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "![f(x, d(y)) ≽ g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≻{rpo} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≽{var} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≽{fun} g(x, x) | y > 0 { y }]\n"));
    pair = setupTheorySimplify(HRelation.GEQ);
    assertTrue(pair.fst().toString().equals(
      "[x + 3 ≽ x + 1 | x > 0 { x }]\n" +
      "[x + 3 ≽{theory} x + 1 | x > 0 { x }]\n"));
    assertTrue(pair.snd().toString().equals(
      "![x + 3 ≽ x + 1 | x > 0 { x }] or " +
      "[x + 3 ≽{theory} x + 1 | x > 0 { x }]\n"));
    pair = setupSimplify("x + 1", "Int", "x + 1", "Int", "Int", "y > 0", HRelation.GEQ, "");
    assertTrue(pair.snd().toString().equals(
      "![x + 1 ≽ x + 1 | y > 0 { }] or " +
      "[x + 1 ≽{equal} x + 1 | y > 0 { }]\n"));
  }

  @Test
  public void testSimplifyGeqNoGr() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify(HRelation.GEQNOGR);
    assertTrue(pair.snd().toString().equals(
      "![f(x, d(y)) ≈ g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≈{var} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≈{fun} g(x, x) | y > 0 { y }]\n"));
    pair = setupTheorySimplify(HRelation.GEQNOGR);
    assertTrue(pair.snd().toString().equals(
      "![x + 3 ≈ x + 1 | x > 0 { x }] or " +
      "[x + 3 ≈{theory} x + 1 | x > 0 { x }]\n"));
    pair = setupSimplify("x + 1", "Int", "x + 1", "Int", "Int", "y > 0", HRelation.GEQNOGR, "");
    assertTrue(pair.snd().toString().equals(
      "![x + 1 ≈ x + 1 | y > 0 { }] or " +
      "[x + 1 ≈{equal} x + 1 | y > 0 { }]\n"));
}

  @Test
  public void testSimplifyRpo() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify(HRelation.RPO);
    assertTrue(pair.snd().toString().equals(
      "![f(x, d(y)) ▷ g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{th} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{select} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{copy} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{ext} g(x, x) | y > 0 { y }]\n"));
  }

  @Test
  public void testSimplifyDistinctTypesAllowed() {
    String trs = "f :: Int -> A g :: Int -> B";
    // you can have different types!
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(x)", "A", "g(x)", "B", "Int",
                                                              "x > 0", HRelation.GEQNOGR, trs);
    assertTrue(pair.snd().toString().equals(
      "![f(x) ≈ g(x) | x > 0 { x }] or " +
      "[f(x) ≈{var} g(x) | x > 0 { x }] or [f(x) ≈{fun} g(x) | x > 0 { x }]\n"));
    pair = setupSimplify("f(x)", "A", "g(x)", "B", "Int", "x > 0", HRelation.GEQ, trs);
    assertTrue(pair.snd().toString().equals(
      "![f(x) ≽ g(x) | x > 0 { x }] or [f(x) ≻{rpo} g(x) | x > 0 { x }] or " +
      "[f(x) ≽{var} g(x) | x > 0 { x }] or [f(x) ≽{fun} g(x) | x > 0 { x }]\n"));
    pair = setupSimplify("f(x)", "A", "g(x)", "B", "Int", "x > 0", HRelation.GREATER, trs);
    assertTrue(pair.snd().toString().equals(
      "![f(x) ≻ g(x) | x > 0 { x }] or [f(x) ≻{rpo} g(x) | x > 0 { x }] or " +
      "[f(x) ≻{var} g(x) | x > 0 { x }] or [f(x) ≻{fun} g(x) | x > 0 { x }]\n"));
  }

  @Test
  public void testSimplifyDistinctTypeStructureNotAllowed() {
    String trs = "f :: Int -> A g :: Int -> B -> B";
    Pair<HorpoConstraintList,SmtProblem> pair;
    pair = setupSimplify("f(x)", "A", "g(x)", "B -> B", "Int", "x > 0", HRelation.GEQNOGR, trs);
    assertTrue(pair.snd().toString().equals("![f(x) ≈ g(x) | x > 0 { x }]\n"));
    pair = setupSimplify("f(x)", "A", "g(x)", "B -> B", "Int", "x > 0", HRelation.GEQ, trs);
    assertTrue(pair.snd().toString().equals("![f(x) ≽ g(x) | x > 0 { x }]\n"));
    pair = setupSimplify("f(x)", "A", "g(x)", "B -> B", "Int", "x > 0", HRelation.GREATER, trs);
    assertTrue(pair.snd().toString().equals("![f(x) ≻ g(x) | x > 0 { x }]\n"));
  }

  @Test
  public void testGeqNoGrTheory() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("y", "Int", "y+x", "Int", "Int",
                                                         "x <= 0", HRelation.GEQNOGRTHEORY, "");
    assertTrue(pair.fst().toString().equals(
      "[y ≈{theory} y + x | x ≤ 0 { y x }]\n" +
      "[y ≽{theory} y + x | x ≤ 0 { y x }]\n" +
      "[y ≻{theory} y + x | x ≤ 0 { y x }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[y ≈{theory} y + x | x ≤ 0 { y x }] == " +
        "([y ≽{theory} y + x | x ≤ 0 { y x }] and " +
        "![y ≻{theory} y + x | x ≤ 0 { y x }])\n"));
  }

  @Test
  public void testGreaterDown() {
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true, false);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+1", "Int", "x-1", "Int", "Int",
                                                        "x >= -4", HRelation.GREATERTHEORY, "");
    assertTrue(pair.fst().toString().equals("[x + 1 ≻{theory} x - 1 | x ≥ -4 { x }]\n"));
    assertTrue(pair.snd().toString().equals("[x + 1 ≻{theory} x - 1 | x ≥ -4 { x }] == [down]\n"));
    assertTrue(solver.queryNumberQuestions() == 2);
    assertTrue(solver.queryQuestion(0).equals(
      "(0 >= 5 + i1) or ((1 + i1 >= i1) and (1001 + i1 >= 0))"));
      // x ≥ -4 ⇒ x + 1 > x - 1 ∧ x + 1 ≥ -1000
    assertTrue(solver.queryQuestion(1).equals(
      "(0 >= 5 + i1) or ((i1 >= 3 + i1) and (999 >= i1))"));
      // x ≥ -4 ⇒ x + 1 < x - 1 ∧ x + 1 ≤ 1000
  }

  @Test
  public void testGreaterNeither() {
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(false, false);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+y", "Int", "y", "Int", "Int",
                                                        "x > y", HRelation.GREATERTHEORY, "");
    assertTrue(pair.fst().toString().equals("[x + y ≻{theory} y | x > y { x y }]\n"));
    assertTrue(pair.snd().toString().equals("![x + y ≻{theory} y | x > y { x y }]\n"));
    assertTrue(solver.queryNumberQuestions() == 2);
    assertTrue(solver.queryQuestion(0).equals(
      "(i2 >= i1) or ((i1 + i2 >= 1 + i2) and (1000 + i1 + i2 >= 0))"));
      // x > y ⇒ x + y > y ∧ x + y ≥ -1000
    assertTrue(solver.queryQuestion(1).equals(
      "(i2 >= i1) or ((i2 >= 1 + i1 + i2) and (1000 >= i1 + i2))"));
      // x > y ⇒ x + y < y ∧ x + y ≤ 1000
  }

  @Test
  public void testGeqUp() {
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(false, true);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+y", "Int", "y", "Int", "Int",
                                                           "x >= 0", HRelation.GEQTHEORY, "");
    assertTrue(pair.fst().toString().equals("[x + y ≽{theory} y | x ≥ 0 { x y }]\n"));
    assertTrue(pair.snd().toString().equals("[x + y ≽{theory} y | x ≥ 0 { x y }] == ![down]\n"));
    assertTrue(solver.queryNumberQuestions() == 2);
    assertTrue(solver.queryQuestion(0).equals("(0 >= 1 + i1) or (i1 + i2 >= i2)"));
      // x ≥ 0 ⇒ x + y ≥ y
    assertTrue(solver.queryQuestion(1).equals("(0 >= 1 + i1) or (i2 >= i1 + i2)"));
      // x ≥ 0 ⇒ y ≥ x + y
  }

  @Test
  public void testGeqBoth() {
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true, true);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+y", "Int", "y", "Int", "Int",
                                                            "x = 0", HRelation.GEQTHEORY, "");
    assertTrue(pair.fst().toString().equals("[x + y ≽{theory} y | x = 0 { x y }]\n"));
    assertTrue(pair.snd().toString().equals("[x + y ≽{theory} y | x = 0 { x y }]\n"));
    assertTrue(solver.queryNumberQuestions() == 2);
    assertTrue(solver.queryQuestion(0).equals("(i1 # 0) or (i1 + i2 >= i2)"));
      // x ≥ 0 ⇒ x + y ≥ y
    assertTrue(solver.queryQuestion(1).equals("(i1 # 0) or (i2 >= i1 + i2)"));
      // x ≥ 0 ⇒ y ≥ x + y
  }

  @Test
  public void testGreaterWhenNotAllVariablesAreConstrained() {
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true, true);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+y", "Int", "x", "Int", "Int",
                                                            "y = 0", HRelation.GEQTHEORY, "");
    assertTrue(pair.snd().toString().equals("![x + y ≽{theory} x | y = 0 { y }]\n"));
    assertTrue(solver.queryNumberQuestions() == 0);
  }

  @Test
  public void testBoolComparisonGeqTrue() {
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(true);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x", "Bool", "x ∧ false", "Bool",
                                                         "Bool", "x", HRelation.GEQTHEORY, "");
    assertTrue(pair.snd().toString().equals("[x ≽{theory} x ∧ false | x { x }]\n"));
    assertTrue(solver.queryNumberQuestions() == 1);
    // x ⇒ x ∨ ¬(x ∧ false)
    assertTrue(solver.queryQuestion(0).equals("!b1 or b1 or !b1 or true"));
  }

  @Test
  public void testBoolComparisonGreaterFalse() {
    FixedAnswerValidityChecker solver = new FixedAnswerValidityChecker(false);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x", "Bool", "x ∨ false", "Bool",
                                                     "Bool", "x", HRelation.GREATERTHEORY, "");
    assertTrue(pair.snd().toString().equals("![x ≻{theory} x ∨ false | x { x }]\n"));
    assertTrue(solver.queryNumberQuestions() == 1);
    // x ⇒ x ∧ ¬(x ∨ false)
    assertTrue(solver.queryQuestion(0).equals("!b1 or (b1 and !b1 and true)"));
  }

  @Test
  public void testTheoryComparisonWrongTheoryTypes() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x", "Bool", "y", "Int", "Int",
                                                           "x", HRelation.GREATERTHEORY, "");
    assertTrue(pair.snd().toString().equals("![x ≻{theory} y | x { x y }]\n"));
  }

  @Test
  public void testVar() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupVarSimplify(HRelation.GEQNOGRVAR);
    assertTrue(pair.snd().toString().equals(
      "![F(c(x), a) ≈{var} F(b, c(x)) | x = 0 { x }] or [c(x) ≈ b | x = 0 { x }]\n" +
      "![F(c(x), a) ≈{var} F(b, c(x)) | x = 0 { x }] or [a ≈ c(x) | x = 0 { x }]\n"));

    pair = setupVarSimplify(HRelation.GEQVAR);
    assertTrue(pair.fst().toString().equals(
      "[F(c(x), a) ≽{var} F(b, c(x)) | x = 0 { x }]\n" +
      "[c(x) ≽ b | x = 0 { x }]\n" +
      "[a ≽ c(x) | x = 0 { x }]\n"));
    assertTrue(pair.snd().toString().equals(
      "![F(c(x), a) ≽{var} F(b, c(x)) | x = 0 { x }] or [c(x) ≽ b | x = 0 { x }]\n" +
      "![F(c(x), a) ≽{var} F(b, c(x)) | x = 0 { x }] or [a ≽ c(x) | x = 0 { x }]\n"));

    pair = setupVarSimplify(HRelation.GREATERVAR);
    assertTrue(pair.fst().toString().equals(
      "[F(c(x), a) ≻{var} F(b, c(x)) | x = 0 { x }]\n" +
      "[c(x) ≽ b | x = 0 { x }]\n" +
      "[a ≽ c(x) | x = 0 { x }]\n" +
      "[c(x) ≻ b | x = 0 { x }]\n" +
      "[a ≻ c(x) | x = 0 { x }]\n"));
    assertTrue(pair.snd().toString().equals(
      // both arguments are oriented
      "![F(c(x), a) ≻{var} F(b, c(x)) | x = 0 { x }] or [c(x) ≽ b | x = 0 { x }]\n" +
      "![F(c(x), a) ≻{var} F(b, c(x)) | x = 0 { x }] or [a ≽ c(x) | x = 0 { x }]\n" +
      // first introduction of the [regardsall] boolean variable
      "![regardsall] or [regards{Q,1}]\n" +
      "![regardsall] or [regards{c,1}]\n" +
      // greatvar can only be used if all arguments are regarded
      "![F(c(x), a) ≻{var} F(b, c(x)) | x = 0 { x }] or [regardsall]\n" +
      // and if at least one of the arguments is strictly oriented
      "![F(c(x), a) ≻{var} F(b, c(x)) | x = 0 { x }] or " +
        "[c(x) ≻ b | x = 0 { x }] or [a ≻ c(x) | x = 0 { x }]\n"));
  }

  private String compCombination(String rel) {
    return
      "[y " + rel + " b | y ≥ 0 { y }]\n[a " + rel + " b | y ≥ 0 { }]\n" +
      "[x " + rel + " b | y ≥ 0 { }]\n[y " + rel + " a | y ≥ 0 { y }]\n" +
      "[a " + rel + " a | y ≥ 0 { }]\n[x " + rel + " a | y ≥ 0 { }]\n" +
      "[y " + rel + " y + 1 | y ≥ 0 { y }]\n[a " + rel + " y + 1 | y ≥ 0 { y }]\n" +
      "[x " + rel + " y + 1 | y ≥ 0 { y }]\n[y " + rel + " c(x) + y | y ≥ 0 { y }]\n" +
      "[a " + rel + " c(x) + y | y ≥ 0 { y }]\n[x " + rel + " c(x) + y | y ≥ 0 { y }]\n";
  }

  /** f and g are equal in the precedence */
  private String equalPred(String startvar) {
    return "!" + startvar + " or ([pred(f)] = [pred(g)])\n";
  }

  /** ∀ i ∈ {1..ar(f)-k}. π{f}(k+i) = π{g}(n+i) or π{g}(n+i) = 0 */
  private String laterArgs(String startvar) {
    return
      "!" + startvar + " or ([pi{g}(5)] = [pi{f}(4)]) or ([pi{g}(5)] = 0)\n" +
      "!" + startvar + " or ([pi{g}(6)] = [pi{f}(5)]) or ([pi{g}(6)] = 0)\n";
  }

  /**
   * χ maps {1..n} ∩ regards[g] into {1..k}, and coincidentally maps disregarded args to 0:
   * ∀ i ∈ {1..4}. 0 ≤ χ(i) ≤ 3 ∧ (reqvar → (if i ∈ regards[g] then χ(i) ≥ 1 else χ(i) = 0))
   */ 
  private String chiDef(String startvar) {
    return
      "[chi1(1)] >= 0\n" +
      "3 >= [chi1(1)]\n" +
        "!" + startvar + " or [regards{g,1}] or ([chi1(1)] = 0)\n" +
        "!" + startvar + " or ![regards{g,1}] or ([chi1(1)] >= 1)\n" +
      "[chi1(2)] >= 0\n" +
      "3 >= [chi1(2)]\n" +
        "!" + startvar + " or [regards{g,2}] or ([chi1(2)] = 0)\n" +
        "!" + startvar + " or ![regards{g,2}] or ([chi1(2)] >= 1)\n" +
      "[chi1(3)] >= 0\n" +
      "3 >= [chi1(3)]\n" +
        "!" + startvar + " or [regards{g,3}] or ([chi1(3)] = 0)\n" +
        "!" + startvar + " or ![regards{g,3}] or ([chi1(3)] >= 1)\n" +
      "[chi1(4)] >= 0\n" +
      "3 >= [chi1(4)]\n" +
        "!" + startvar + " or [regards{g,4}] or ([chi1(4)] = 0)\n" +
        "!" + startvar + " or ![regards{g,4}] or ([chi1(4)] >= 1)\n";
  }

  /**
   * χ is injective on {1..n} ∩ regards[g]: ∀ i ∈ {1..4}. ∀ j ∈ {i+1..4}. i ∈ regards[g] ⇒ χ(i) != χ(j)
   * (this suffices because if j ∉ regards[g], then χ(j) = 0 != χ(i) regardless)
   */
  private String injective(String startvar) {
    return
      "!" + startvar + " or ![regards{g,1}] or ([chi1(1)] # [chi1(2)])\n" +
      "!" + startvar + " or ![regards{g,1}] or ([chi1(1)] # [chi1(3)])\n" +
      "!" + startvar + " or ![regards{g,1}] or ([chi1(1)] # [chi1(4)])\n" +
      "!" + startvar + " or ![regards{g,2}] or ([chi1(2)] # [chi1(3)])\n" +
      "!" + startvar + " or ![regards{g,2}] or ([chi1(2)] # [chi1(4)])\n" +
      "!" + startvar + " or ![regards{g,3}] or ([chi1(3)] # [chi1(4)])\n";
  }

  /**
   * whenever χ(i) ∈ {1..k} then π{f}(χ(i)) = π{g}(i) (this also implies that regarded elements
   * of g are mapped to regarded elements of f, as π{f}(j) = 0 when j ∉ regards[f]
   */
  private String samePi(String startvar) {
    return
      "!" + startvar + " or ([chi1(1)] # 1) or ([pi{f}(1)] = [pi{g}(1)])\n" +
      "!" + startvar + " or ([chi1(1)] # 2) or ([pi{f}(2)] = [pi{g}(1)])\n" +
      "!" + startvar + " or ([chi1(1)] # 3) or ([pi{f}(3)] = [pi{g}(1)])\n" +
      "!" + startvar + " or ([chi1(2)] # 1) or ([pi{f}(1)] = [pi{g}(2)])\n" +
      "!" + startvar + " or ([chi1(2)] # 2) or ([pi{f}(2)] = [pi{g}(2)])\n" +
      "!" + startvar + " or ([chi1(2)] # 3) or ([pi{f}(3)] = [pi{g}(2)])\n" +
      "!" + startvar + " or ([chi1(3)] # 1) or ([pi{f}(1)] = [pi{g}(3)])\n" +
      "!" + startvar + " or ([chi1(3)] # 2) or ([pi{f}(2)] = [pi{g}(3)])\n" +
      "!" + startvar + " or ([chi1(3)] # 3) or ([pi{f}(3)] = [pi{g}(3)])\n" +
      "!" + startvar + " or ([chi1(4)] # 1) or ([pi{f}(1)] = [pi{g}(4)])\n" +
      "!" + startvar + " or ([chi1(4)] # 2) or ([pi{f}(2)] = [pi{g}(4)])\n" +
      "!" + startvar + " or ([chi1(4)] # 3) or ([pi{f}(3)] = [pi{g}(4)])\n";
  }

  /** ∀ i ∈ {1..n} ∩ regards[g]. left_{χ(i)} <relation> right_i */
  private String allGeq(String startvar, String relation) {
    return
      "!" + startvar + " or ([chi1(1)] # 1) or [y " + relation + " b | y ≥ 0 { y }]\n" +
      "!" + startvar + " or ([chi1(1)] # 2) or [a " + relation + " b | y ≥ 0 { }]\n" +
      "!" + startvar + " or ([chi1(1)] # 3) or [x " + relation + " b | y ≥ 0 { }]\n" +
      "!" + startvar + " or ([chi1(2)] # 1) or [y " + relation + " a | y ≥ 0 { y }]\n" +
      "!" + startvar + " or ([chi1(2)] # 2) or [a " + relation + " a | y ≥ 0 { }]\n" +
      "!" + startvar + " or ([chi1(2)] # 3) or [x " + relation + " a | y ≥ 0 { }]\n" +
      "!" + startvar + " or ([chi1(3)] # 1) or [y " + relation + " y + 1 | y ≥ 0 { y }]\n" +
      "!" + startvar + " or ([chi1(3)] # 2) or [a " + relation + " y + 1 | y ≥ 0 { y }]\n" +
      "!" + startvar + " or ([chi1(3)] # 3) or [x " + relation + " y + 1 | y ≥ 0 { y }]\n" +
      "!" + startvar + " or ([chi1(4)] # 1) or [y " + relation + " c(x) + y | y ≥ 0 { y }]\n" +
      "!" + startvar + " or ([chi1(4)] # 2) or [a " + relation + " c(x) + y | y ≥ 0 { y }]\n" +
      "!" + startvar + " or ([chi1(4)] # 3) or [x " + relation + " c(x) + y | y ≥ 0 { y }]\n";
  }

  /** ∃ j ∈ {1..k} ∩ regards[f]. ∀ i ∈ {1..n}. χ(i) = j ⇒ left_j ≻ right_i */
  private String greaterReqs(String startvar) {
    return
      "[decrease1] >= 1\n" +
      "3 >= [decrease1]\n" +
      "!" + startvar + " or ([decrease1] # 1) or [regards{f,1}]\n"+
      "!" + startvar + " or ([decrease1] # 2) or [regards{f,2}]\n"+
      "!" + startvar + " or ([decrease1] # 3) or [regards{f,3}]\n"+
      "!" + startvar + " or ([chi1(1)] # [decrease1]) or ([decrease1] # 1) or [y ≻ b | y ≥ 0 { y }]\n"+
      "!" + startvar + " or ([chi1(1)] # [decrease1]) or ([decrease1] # 2) or [a ≻ b | y ≥ 0 { }]\n"+
      "!" + startvar + " or ([chi1(1)] # [decrease1]) or ([decrease1] # 3) or [x ≻ b | y ≥ 0 { }]\n"+
      "!" + startvar + " or ([chi1(2)] # [decrease1]) or ([decrease1] # 1) or [y ≻ a | y ≥ 0 { y }]\n"+
      "!" + startvar + " or ([chi1(2)] # [decrease1]) or ([decrease1] # 2) or [a ≻ a | y ≥ 0 { }]\n"+
      "!" + startvar + " or ([chi1(2)] # [decrease1]) or ([decrease1] # 3) or [x ≻ a | y ≥ 0 { }]\n"+
      "!" + startvar + " or ([chi1(3)] # [decrease1]) or ([decrease1] # 1) or [y ≻ y + 1 | y ≥ 0 { y }]\n"+
      "!" + startvar + " or ([chi1(3)] # [decrease1]) or ([decrease1] # 2) or [a ≻ y + 1 | y ≥ 0 { y }]\n"+
      "!" + startvar + " or ([chi1(3)] # [decrease1]) or ([decrease1] # 3) or [x ≻ y + 1 | y ≥ 0 { y }]\n"+
      "!" + startvar + " or ([chi1(4)] # [decrease1]) or ([decrease1] # 1) or [y ≻ c(x) + y | y ≥ 0 { y }]\n"+
      "!" + startvar + " or ([chi1(4)] # [decrease1]) or ([decrease1] # 2) or [a ≻ c(x) + y | y ≥ 0 { y }]\n"+
      "!" + startvar + " or ([chi1(4)] # [decrease1]) or ([decrease1] # 3) or [x ≻ c(x) + y | y ≥ 0 { y }]\n";
  }

  private String isSurjective(String startvar) {
    return
      "!" + startvar + " or ![regards{f,1}] or ([chi1(1)] = 1) or ([chi1(2)] = 1) or ([chi1(3)] = 1) or ([chi1(4)] = 1)\n" +
      "!" + startvar + " or ![regards{f,2}] or ([chi1(1)] = 2) or ([chi1(2)] = 2) or ([chi1(3)] = 2) or ([chi1(4)] = 2)\n" +
      "!" + startvar + " or ![regards{f,3}] or ([chi1(1)] = 3) or ([chi1(2)] = 3) or ([chi1(3)] = 3) or ([chi1(4)] = 3)\n";
  }

  @Test
  public void testFun() {
    Pair<HorpoConstraintList,SmtProblem> p;
    String trs = "f :: Int -> A -> A -> Int -> A -> Unit\n" +
                 "g :: A -> A -> Int -> Int -> B -> A -> B\n" +
                 "a :: A\nb :: A\nc :: A -> Int\n";

    // ≽ functions as expected
    p = setupSimplify("f(y, a, x)", "Int -> A -> Unit", "g(b, a, y+1, c(x) + y)", "B -> A -> B",
                      "Int", "y >= 0", HRelation.GEQFUN, trs);
    String startvar = "[f(y, a, x) ≽{fun} g(b, a, y + 1, c(x) + y) | y ≥ 0 { y }]";
    assertTrue(p.fst().toString().equals(startvar + "\n" + compCombination("≽")));
    assertTrue(p.snd().toString().equals(
      equalPred(startvar) +
      laterArgs(startvar) +
      chiDef(startvar) +
      injective(startvar) +
      samePi(startvar) +
      allGeq(startvar, "≽")
    ));

    // ≻ functions as expected
    p = setupSimplify("f(y, a, x)", "Int -> A -> Unit", "g(b, a, y+1, c(x) + y)", "B -> A -> B",
                      "Int", "y >= 0", HRelation.GREATERFUN, trs);
    startvar = "[f(y, a, x) ≻{fun} g(b, a, y + 1, c(x) + y) | y ≥ 0 { y }]";
    assertTrue(p.fst().toString().equals(startvar + "\n" + compCombination("≽") +
                                         compCombination("≻")));
    assertTrue(p.snd().toString().equals(
      equalPred(startvar) +
      laterArgs(startvar) +
      chiDef(startvar) +
      injective(startvar) +
      samePi(startvar) +
      allGeq(startvar, "≽") +
      greaterReqs(startvar)
    ));

    // ≈ functions as expected
    p = setupSimplify("f(y, a, x)", "Int -> A -> Unit", "g(b, a, y+1, c(x) + y)", "B -> A -> B",
                      "Int", "y >= 0", HRelation.GEQNOGRFUN, trs);
    startvar = "[f(y, a, x) ≈{fun} g(b, a, y + 1, c(x) + y) | y ≥ 0 { y }]";
    assertTrue(p.fst().toString().equals(startvar + "\n" + compCombination("≈")));
    assertTrue(p.snd().toString().equals(
      equalPred(startvar) +
      laterArgs(startvar) +
      chiDef(startvar) +
      injective(startvar) +
      samePi(startvar) +
      allGeq(startvar, "≈") +
      isSurjective(startvar)
    ));
  }

  @Test
  public void testFunEmptyLeft() {
    Pair<HorpoConstraintList,SmtProblem> p;
    String trs = "f :: A -> Unit\n" +
                 "g :: A -> A -> Int -> Int\n" +
                 "a :: A\nb :: A\n\n";

    p = setupSimplify("f", "A -> Unit", "g(b, a)", "Int -> Int", "Int", "true",
                      HRelation.GEQNOGRFUN, trs);
    String startvar = "[f ≈{fun} g(b, a) | true { }]";
    assertTrue(p.snd().toString().equals(
      // root symbols are equal
      "!" + startvar + " or ([pred(f)] = [pred(g)])\n" +
      // additional arguments are mapped to the same π
      "!" + startvar + " or ([pi{g}(3)] = [pi{f}(1)]) or ([pi{g}(3)] = 0)\n" +
      // χ must map everything to 0 (which means the arguments must be disregarded)
      "[chi1(1)] >= 0\n" +
      "0 >= [chi1(1)]\n" +
      "!" + startvar + " or [regards{g,1}] or ([chi1(1)] = 0)\n" +
      "!" + startvar + " or ![regards{g,1}] or ([chi1(1)] >= 1)\n" +
      "[chi1(2)] >= 0\n" +
      "0 >= [chi1(2)]\n" +
      "!" + startvar + " or [regards{g,2}] or ([chi1(2)] = 0)\n" +
      "!" + startvar + " or ![regards{g,2}] or ([chi1(2)] >= 1)\n"));

    p = setupSimplify("f", "A -> Unit", "g(b, a)", "Int -> Int", "Int", "true",
                      HRelation.GREATERFUN, trs);
    assertTrue(p.snd().toString().equals("![f ≻{fun} g(b, a) | true { }]\n"));
  }

  @Test
  public void testFunEmptyRight() {
    Pair<HorpoConstraintList,SmtProblem> p;
    String trs = "f :: A -> Unit\n" +
                 "g :: A -> A -> Int -> Int\n" +
                 "a :: A\nb :: A\n\n";

    p = setupSimplify("g(b, a)", "Int -> Int", "f", "A -> Unit", "Int", "true",
                      HRelation.GEQNOGRFUN, trs);
    String startvar = "[g(b, a) ≈{fun} f | true { }]";
    assertTrue(p.snd().toString().equals(
      // root symbols are equal
      "!" + startvar + " or ([pred(g)] = [pred(f)])\n" +
      // additional arguments are mapped to the same π
      "!" + startvar + " or ([pi{f}(1)] = [pi{g}(3)]) or ([pi{f}(1)] = 0)\n" +
      // no requirements on χ, since χ is necessarily empty, but we do have a surjectivity
      // requirement -- which means that the arguments on the right cannot be regarded!
      "!" + startvar + " or ![regards{g,1}]\n" +
      "!" + startvar + " or ![regards{g,2}]\n"
    ));

    p = setupSimplify("g(b, a)", "Int -> Int", "f", "A -> Unit", "Int", "true",
                      HRelation.GREATERFUN, trs);
    startvar = "[g(b, a) ≻{fun} f | true { }]";
    assertTrue(p.snd().toString().equals(
      // root symbols are equal
      "!" + startvar + " or ([pred(g)] = [pred(f)])\n" +
      // additional arguments are mapped to the same π
      "!" + startvar + " or ([pi{f}(1)] = [pi{g}(3)]) or ([pi{f}(1)] = 0)\n" +
      // some argument must decrease -- either argument 1 or argument 2!
      "[decrease1] >= 1\n" +
      "2 >= [decrease1]\n" +
      // for the decreasing argument, we only need it to be regarded, and this suffices!
      "!" + startvar + " or ([decrease1] # 1) or [regards{g,1}]\n" +
      "!" + startvar + " or ([decrease1] # 2) or [regards{g,2}]\n"
    ));
  }

  @Test
  public void testEquality() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f", "A -> A", "f", "A -> A", "Int",
                                                       "true", HRelation.GEQEQUAL, "f :: A -> A");
    assertTrue(pair.fst().toString().equals("[f ≽{equal} f | true { }]\n"));
    assertTrue(pair.snd().toString().equals("[f ≽{equal} f | true { }]\n"));
  }

  @Test
  public void testGreaterRpo() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(1)", "Int", "g(2)", "Int", "Int",
                                  "true", HRelation.GREATERRPO, "f :: Int -> Int g :: Int -> Int");
    assertTrue(pair.snd().toString().equals(
      "![f(1) ≻{rpo} g(2) | true { }] or [f(1) ▷ g(2) | true { }]\n"));

    pair = setupSimplify("f(1)", "Int -> Int -> Int", "3", "Int", "Int", "true",
                         HRelation.GREATERRPO, "f :: Int -> Int -> Int -> Int");
    assertTrue(pair.snd().toString().equals(
      "![f(1) ≻{rpo} 3 | true { }] or [regards{f,2}]\n" +
      "![f(1) ≻{rpo} 3 | true { }] or [regards{f,3}]\n" +
      "![f(1) ≻{rpo} 3 | true { }] or [f(1) ▷ 3 | true { }]\n"));

    pair = setupSimplify("x + 3", "Int", "x", "Int", "Int", "x > 0", HRelation.GREATERRPO, "");
    assertTrue(pair.snd().toString().equals("![x + 3 ≻{rpo} x | x > 0 { x }]\n"));
  }

  @Test
  public void testRpoSelectBaseRight() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(x,a,z)", "Unit", "c(a)", "A",
      "Int", "true", HRelation.RPOSELECT,
      "f :: (Int -> Bool) -> A -> (Int -> A -> Int) -> Unit\nc :: A -> A\na :: A");
    assertTrue(pair.snd().toString().equals(
      "![f(x, a, z) ▷{select} c(a) | true { }] or " +
      "([regards{f,1}] and [x ≽ c | true { }] and [f(x, a, z) ▷ a | true { }]) or " +
      "([regards{f,2}] and [a ≽ c(a) | true { }])\n"));
  }

  @Test
  public void testRpoSelectHigherRight() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(x,a,z)", "Unit", "c(a)",
      "(A -> A) -> C", "Int", "true", HRelation.RPOSELECT,
      "f :: (Int -> Bool) -> A -> (Int -> A -> Int) -> Unit\nc :: A -> (A -> A) -> C\na :: A");
    assertTrue(pair.snd().toString().equals(
      "![f(x, a, z) ▷{select} c(a) | true { }] or " +
      "([regards{f,1}] and [x ≽ c(a) | true { }]) or " +
      "([regards{f,3}] and [z ≽ c | true { }] and [f(x, a, z) ▷ a | true { }])\n"));
  }

  @Test
  public void testCopy() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(a)", "Int", "g(b,x)", "Int", "Int",
              "true", HRelation.RPOCOPY, "f :: Int -> Int g :: Int -> Int -> Int a :: Int b :: Int");
    assertTrue(pair.snd().toString().equals(
      "![f(a) ▷{copy} g(b, x) | true { }] or ([pred(f)] >= 1 + [pred(g)])\n" +
      "![f(a) ▷{copy} g(b, x) | true { }] or ![regards{g,1}] or [f(a) ▷ b | true { }]\n" +
      "![f(a) ▷{copy} g(b, x) | true { }] or ![regards{g,2}] or [f(a) ▷ x | true { }]\n"));
  }

  @Test
  public void testFailedCopy() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(a)", "Int", "f(b)", "Int", "Int",
                                   "true", HRelation.RPOCOPY, "f :: Int -> Int a :: Int b :: Int");
    assertTrue(pair.snd().toString().equals("![f(a) ▷{copy} f(b) | true { }]\n"));
  }

  @Test
  public void testRpoTheory() {
    // values
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("a", "Int", "true", "Bool", "Int",
                                                           "true", HRelation.RPOTH, "a :: Int");
    assertTrue(pair.snd().toString().equals("[a ▷{th} true | true { }]\n"));
    // complex expressions with variable in theory
    pair = setupSimplify("a", "A", "x + y/2", "Int", "Int", "x > 0", HRelation.RPOTH, "a :: A");
    assertTrue(pair.snd().toString().equals("[a ▷{th} x + y / 2 | x > 0 { x y }]\n"));
    // non-example: a variable that is not in the theory
    pair = setupSimplify("a", "A", "x", "Int", "Int", "y > 0", HRelation.RPOTH, "a :: A");
    assertTrue(pair.snd().toString().equals("![a ▷{th} x | y > 0 { }]\n"));
  }

  @Test
  public void testFailedExt() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(F,x)", "A", "F(x)", "A", "Int",
                                       "x > 0", HRelation.RPOEXT, "f :: (Int -> A) -> Int -> A");
    assertTrue(pair.snd().toString().equals("![f(F, x) ▷{ext} F(x) | x > 0 { x }]\n"));
  }

  @Test
  public void testExtWithZeroArguments() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f", "Int -> B", "g(0)" ,"B", "Int",
                                        "true", HRelation.RPOEXT, "f :: Int -> B\ng :: Int -> B");
    assertTrue(pair.snd().toString().equals("![f ▷{ext} g(0) | true { }]\n"));
  }

  @Test
  public void testExtWithOneArgument() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(x,y)", "A", "g(y)" ,"B", "Int",
                                 "true", HRelation.RPOEXT, "f :: Int -> Int -> A g :: Int -> B");
    String startvar = "[f(x, y) ▷{ext} g(y) | true { y }]";
    assertTrue(pair.snd().toString().equals(
      // create a ∈ {1..2} (arity of f)
      "[decr1] >= 1\n2 >= [decr1]\n" +
      // create χ(1) ∈ {0..2}
      "[chi1(1)] >= 0\n2 >= [chi1(1)]\n" +
      // require that χ(1) > 0 if and only if regards{g,1} ∧ a ≥ π{g}(1) (that is, 1 ≤ π{g}(1) ≤ a)
      "!" + startvar + " or [regards{g,1}] or ([chi1(1)] = 0)\n" +
      "!" + startvar + " or ([decr1] >= [pi{g}(1)]) or ([chi1(1)] = 0)\n" +
      "!" + startvar + " or ![regards{g,1}] or ([pi{g}(1)] >= 1 + [decr1]) or ([chi1(1)] >= 1)\n" +
      // j ∈ strict can only hold when π{f}(j) = a
      "!" + startvar + " or ![strict1_1] or ([pi{f}(1)] = [decr1])\n" +
      "!" + startvar + " or ![strict1_2] or ([pi{f}(2)] = [decr1])\n" +
      // at least one position is oriented strictly
      "!" + startvar + " or [strict1_1] or [strict1_2]\n" +
      // the function symbols have the same precedence
      "!" + startvar + " or ([pred(f)] = [pred(g)])\n" +
      // for i = 1: if χ(i) != 0 (so 1 ≤ π{g}(i) ≤ a) then π{f}(χ(i)) = π{g}(i)
      "!" + startvar + " or ([chi1(1)] # 1) or ([pi{f}(1)] = [pi{g}(1)])\n" +
      "!" + startvar + " or ([chi1(1)] # 2) or ([pi{f}(2)] = [pi{g}(1)])\n" +
      // l ▷ the one argument on the right
      "!" + startvar + " or ![regards{g,1}] or [f(x, y) ▷ y | true { y }]\n" +
      // always left_{χ(i)} ≽ right_{i}
      "!" + startvar + " or ([chi1(1)] # 1) or [x ≽ y | true { y }]\n" +
      "!" + startvar + " or ([chi1(1)] # 2) or [y ≽ y | true { y }]\n" +
      // if χ(i) ∈ strict then left_{χ(i)} ≻ right_{i}
      "!" + startvar + " or ![strict1_1] or ([chi1(1)] # 1) or [x ≻ y | true { y }]\n" +
      "!" + startvar + " or ![strict1_2] or ([chi1(1)] # 2) or [y ≻ y | true { y }]\n"));
  }

  @Test
  public void testExtWithMultipleArguments() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(a,b,c)", "A", "g(u,v,w,x)" ,"A",
             "Int", "true", HRelation.RPOEXT, "f :: B -> B -> B -> A g :: B -> B -> B -> B -> A");
    String startvar = "[f(a, b, c) ▷{ext} g(u, v, w, x) | true { }]";

    StringBuilder req = new StringBuilder();
    // create a ∈ {1..3} (arity of f)
    req.append("[decr1] >= 1\n3 >= [decr1]\n");
    // for i ∈ {1..4}. create χ(1) ∈ {0..3} and require that χ(i) > 0 if and only if regards{g,i} ∧ a ≥ π{g}(i)
    for (int i = 1; i <= 4; i++) {
      req.append(
        "[chi1(" + i + ")] >= 0\n3 >= [chi1(" + i + ")]\n" +
        "!" + startvar + " or [regards{g," + i + "}] or ([chi1(" + i + ")] = 0)\n" +
        "!" + startvar + " or ([decr1] >= [pi{g}(" + i + ")]) or ([chi1(" + i + ")] = 0)\n" +
        "!" + startvar + " or ![regards{g," + i + "}] or ([pi{g}(" + i + ")] >= 1 + [decr1]) or ([chi1(" + i + ")] >= 1)\n");
    }
    // for j ∈ {1..3}. j ∈ strict can only hold when π{f}(j) = a
    for (int j = 1; j <= 3; j++) {
      req.append("!" + startvar + " or ![strict1_" + j + "] or ([pi{f}(" + j + ")] = [decr1])\n");
    }
    // at least one position is oriented strictly
    req.append("!" + startvar + " or [strict1_1] or [strict1_2] or [strict1_3]\n");
    // the function symbols have the same precedence
    req.append("!" + startvar + " or ([pred(f)] = [pred(g)])\n");
    // for i ∈ {1..4}: if χ(i) != 0 (so 1 ≤ π{g}(i) ≤ a) then π{f}(χ(i)) = π{g}(i)
    for (int i = 1; i <= 4; i++) {
      for (int j = 1; j <= 3; j++) {
        req.append("!" + startvar + " or ([chi1(" + i + ")] # " + j + ") or " +
          "([pi{f}(" + j + ")] = [pi{g}(" + i + ")])\n");
      }
    }
    // l ▷ all arguments on the right
    req.append(
      "!" + startvar + " or ![regards{g,1}] or [f(a, b, c) ▷ u | true { }]\n" +
      "!" + startvar + " or ![regards{g,2}] or [f(a, b, c) ▷ v | true { }]\n" +
      "!" + startvar + " or ![regards{g,3}] or [f(a, b, c) ▷ w | true { }]\n" +
      "!" + startvar + " or ![regards{g,4}] or [f(a, b, c) ▷ x | true { }]\n"
    );
    // always left_{χ(i)} ≽ right_{i}
    req.append(
      "!" + startvar + " or ([chi1(1)] # 1) or [a ≽ u | true { }]\n" +
      "!" + startvar + " or ([chi1(1)] # 2) or [b ≽ u | true { }]\n" +
      "!" + startvar + " or ([chi1(1)] # 3) or [c ≽ u | true { }]\n" +
      "!" + startvar + " or ([chi1(2)] # 1) or [a ≽ v | true { }]\n" +
      "!" + startvar + " or ([chi1(2)] # 2) or [b ≽ v | true { }]\n" +
      "!" + startvar + " or ([chi1(2)] # 3) or [c ≽ v | true { }]\n" +
      "!" + startvar + " or ([chi1(3)] # 1) or [a ≽ w | true { }]\n" +
      "!" + startvar + " or ([chi1(3)] # 2) or [b ≽ w | true { }]\n" +
      "!" + startvar + " or ([chi1(3)] # 3) or [c ≽ w | true { }]\n" +
      "!" + startvar + " or ([chi1(4)] # 1) or [a ≽ x | true { }]\n" +
      "!" + startvar + " or ([chi1(4)] # 2) or [b ≽ x | true { }]\n" +
      "!" + startvar + " or ([chi1(4)] # 3) or [c ≽ x | true { }]\n"
    );
    // if χ(i) ∈ strict then left_{χ(i)} ≻ right_{i}
    req.append(
      "!" + startvar + " or ![strict1_1] or ([chi1(1)] # 1) or [a ≻ u | true { }]\n" +
      "!" + startvar + " or ![strict1_2] or ([chi1(1)] # 2) or [b ≻ u | true { }]\n" +
      "!" + startvar + " or ![strict1_3] or ([chi1(1)] # 3) or [c ≻ u | true { }]\n" +
      "!" + startvar + " or ![strict1_1] or ([chi1(2)] # 1) or [a ≻ v | true { }]\n" +
      "!" + startvar + " or ![strict1_2] or ([chi1(2)] # 2) or [b ≻ v | true { }]\n" +
      "!" + startvar + " or ![strict1_3] or ([chi1(2)] # 3) or [c ≻ v | true { }]\n" +
      "!" + startvar + " or ![strict1_1] or ([chi1(3)] # 1) or [a ≻ w | true { }]\n" +
      "!" + startvar + " or ![strict1_2] or ([chi1(3)] # 2) or [b ≻ w | true { }]\n" +
      "!" + startvar + " or ![strict1_3] or ([chi1(3)] # 3) or [c ≻ w | true { }]\n" +
      "!" + startvar + " or ![strict1_1] or ([chi1(4)] # 1) or [a ≻ x | true { }]\n" +
      "!" + startvar + " or ![strict1_2] or ([chi1(4)] # 2) or [b ≻ x | true { }]\n" +
      "!" + startvar + " or ![strict1_3] or ([chi1(4)] # 3) or [c ≻ x | true { }]\n"
    );
    // ∀ i1 ∈ {1..3}, i2 ∈ {i1+1..4}: if χ(i1) = χ(i2) != 0 then χ(i1) ∈ strict
    for (int i1 = 1; i1 <= 3; i1++) {
      for (int i2 = i1+1; i2 <= 4; i2++) {
        for (int j = 1; j <= 3; j++) {
          req.append("!" + startvar + " or ([chi1(" + i1 + ")] # " + j + ") or " +
            "([chi1(" + i2 + ")] # " + j + ") or [strict1_" + j + "]\n");
        }
      }
    }
    assertTrue(pair.snd().toString().equals(req.toString()));
  }
}

