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

package cora.termination.reduction_pairs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.smt.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.config.Settings;
import cora.termination.reduction_pairs.HorpoConstraintList.Relation;

public class HorpoConstraintListTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt);
  }

  private Type type(String txt) {
    return CoraInputReader.readType(txt);
  }

  private HorpoConstraintList makeList(HorpoParameters param, TRS trs) {
    return new HorpoConstraintList(param, new TermPrinter(trs.queryAlphabet().getSymbols().stream()
                                      .map(FunctionSymbol::queryName).collect(Collectors.toSet())));
  }

  @Test
  public void testStoreDifferentThings() {
    TRS trs = makeTrs("f :: Int -> Int -> Int g :: Int -> Int -> Int d :: Int -> Int");
    HorpoConstraintList lst = makeList(new HorpoParameters(1000, true), trs);
    Rule rule = CoraInputReader.readRule("f(x, d(y)) -> g(x,x) | x > 0", trs);
    BVar x1 = lst.store(rule.queryLeftSide(), HorpoConstraintList.StartRelation.Greater,
                        rule.queryRightSide(), rule.queryConstraint());
    rule = CoraInputReader.readRule("g(x, d(x)) -> f(y,x)", trs);
    Term right = rule.queryRightSide();
    TreeSet<Variable> vars = new TreeSet<Variable>(
      Set.of(right.querySubterm(Position.parse("1")).queryVariable(),
      TermFactory.createVar("z", type("Int")))
    );
    BVar x2 = lst.getVariableFor(rule.queryLeftSide(), Relation.GEQMONO, right,
                                 rule.queryConstraint(), vars);
    assertTrue(x1 != x2);
    assertTrue(lst.toString().equals(
      "@ [f(x, d(y)) ≻ g(x, x) | x > 0 { x }]\n" +
      "@ [g(x, d(x)) ≽{mono} f(y, x) | true { y }]\n"));
  }

  @Test
  public void testStoreTheSameThing() {
    TRS trs = makeTrs("f :: Int -> Int -> Int g :: Int -> Int -> Int d :: Int -> Int");
    HorpoConstraintList lst = makeList(new HorpoParameters(1000, false), trs);
    Rule rule = CoraInputReader.readRule("f(x, d(y)) -> g(x,x) | x > 0", trs);
    BVar x1 = lst.store(rule.queryLeftSide(), HorpoConstraintList.StartRelation.Greater,
                        rule.queryRightSide(), rule.queryConstraint());
    rule = CoraInputReader.readRule("f(x, d(y)) -> g(x,x) | x > 0", trs);
    TreeSet<Variable> vars = new TreeSet<Variable>();
    for (Variable x : rule.queryRightSide().vars()) vars.add(x);
    vars.add(TermFactory.createVar("z", type("Int")));
    BVar x2 = lst.getVariableFor(rule.queryLeftSide(), Relation.GREATER,
                                 rule.queryRightSide(), rule.queryConstraint(), vars);
    assertTrue(x1 == x2);
    assertTrue(lst.toString().equals("@ [f(x, d(y)) ≻ g(x, x) | x > 0 { x }]\n"));
  }

  /**
   * This sets up a simplification problem l <relation> r | phi { x1,...,xn,y }, where l and r have
   * the given types and x1,...,xn are the variables of phi.  Then, it does a single simplification
   * step.
   * Both the resulting list and the corresponding state of the SmtProblem are returned.
   */
  private Pair<HorpoConstraintList,SmtProblem> setupSimplify(String l, String lsort, String r,
                  String rsort, String ysort, String phi, Relation relation, String trsstring) {
    TRS trs = makeTrs("Q :: (" + lsort + ") -> (" + rsort + ") -> (" + ysort + ") -> Bool -> unit"
                      + "\n" + trsstring);
    HorpoParameters param = new HorpoParameters(1000, false);
    HorpoConstraintList lst = makeList(param, trs);
    Term term = CoraInputReader.readTerm("Q(" + l + ", " + r + ", y, " + phi + ")", trs);
    Term left = term.queryArgument(1);
    Term right = term.queryArgument(2);
    Term constraint = term.queryArgument(4);
    Variable y = term.queryArgument(3).queryVariable();
    TreeSet<Variable> tvar = new TreeSet<Variable>();
    tvar.add(y);
    for (Variable x : constraint.vars()) tvar.add(x);
    lst.getVariableFor(left, relation, right, constraint, tvar);
    lst.simplify();
    return new Pair<HorpoConstraintList,SmtProblem>(lst, param.queryProblem());
  }

  /**
   * This sets up a simplification problem of the form f(x, d(y)) REL g(x, x) | x > 0 { x },
   * and does a single simplification step.  Here, REL is the given relation.
   * Both the resulting list and the corresponding state of the SmtPorblem are returned.
   */
  private Pair<HorpoConstraintList,SmtProblem> setupSimplify(Relation relation) {
    return setupSimplify("f(x, d(y))", "Int", "g(x,x)", "Int", "Int", "y > 0", relation,
                         "f :: Int -> Int -> Int g :: Int -> Int -> Int d :: Int -> Int");
  }

  /**
   * This sets up a simplification problem of the form x+3 REL x+1 | x > 0 { x },
   * and does a single simplification step.  Here, REL is the given relation.
   * Both the resulting list and the corresponding state of the SmtPorblem are returned.
   */
  private Pair<HorpoConstraintList,SmtProblem> setupTheorySimplify(Relation relation) {
    return setupSimplify("x+3", "Int", "x+1", "Int", "Int", "x > 0", relation, "");
  }

  @Test
  public void testSimplifyGreater() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify(Relation.GREATER);
    assertTrue(pair.fst().toString().equals(
      "$ [f(x, d(y)) ≻ g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ≻{rpo} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ≻{mono} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ≻{args} g(x, x) | y > 0 { y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [f(x, d(y)) ≻ g(x, x) | y > 0 { y }]) or " +
      "[f(x, d(y)) ≻{rpo} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≻{mono} g(x, x) | y > 0 { y }] or "+
      "[f(x, d(y)) ≻{args} g(x, x) | y > 0 { y }]\n"));
    pair = setupTheorySimplify(Relation.GREATER);
    assertTrue(pair.fst().toString().equals(
      "$ [x + 3 ≻ x + 1 | x > 0 { x }]\n" +
      "@ [x + 3 ≻{theory} x + 1 | x > 0 { x }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [x + 3 ≻ x + 1 | x > 0 { x }]) or " +
      "[x + 3 ≻{theory} x + 1 | x > 0 { x }]\n"));
  }

  @Test
  public void testSimplifyGeq() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify(Relation.GEQ);
    assertTrue(pair.fst().toString().equals(
      "$ [f(x, d(y)) ≽ g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ≻{rpo} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ≽{mono} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ≽{args} g(x, x) | y > 0 { y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [f(x, d(y)) ≽ g(x, x) | y > 0 { y }]) or " +
      "[f(x, d(y)) ≻{rpo} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≽{mono} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≽{args} g(x, x) | y > 0 { y }]\n"));
    pair = setupTheorySimplify(Relation.GEQ);
    assertTrue(pair.fst().toString().equals(
      "$ [x + 3 ≽ x + 1 | x > 0 { x }]\n" +
      "@ [x + 3 ≽{theory} x + 1 | x > 0 { x }]\n" +
      "@ [x + 3 ≽{equal} x + 1 | x > 0 { x }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [x + 3 ≽ x + 1 | x > 0 { x }]) or " +
      "[x + 3 ≽{theory} x + 1 | x > 0 { x }] or " +
      "[x + 3 ≽{equal} x + 1 | x > 0 { x }]\n"));
  }

  @Test
  public void testSimplifyGeqNoGr() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify(Relation.GEQNOGR);
    assertTrue(pair.fst().toString().equals(
      "$ [f(x, d(y)) ≈ g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ≈{mono} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ≈{args} g(x, x) | y > 0 { y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [f(x, d(y)) ≈ g(x, x) | y > 0 { y }]) or " +
      "[f(x, d(y)) ≈{mono} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ≈{args} g(x, x) | y > 0 { y }]\n"));
    pair = setupTheorySimplify(Relation.GEQNOGR);
    assertTrue(pair.fst().toString().equals(
      "$ [x + 3 ≈ x + 1 | x > 0 { x }]\n" +
      "@ [x + 3 ≈{theory} x + 1 | x > 0 { x }]\n" +
      "@ [x + 3 ≈{equal} x + 1 | x > 0 { x }]\n"));
      assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [x + 3 ≈ x + 1 | x > 0 { x }]) or " +
      "[x + 3 ≈{theory} x + 1 | x > 0 { x }] or " +
      "[x + 3 ≈{equal} x + 1 | x > 0 { x }]\n"));
}

  @Test
  public void testSimplifyRpo() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify(Relation.RPO);
    assertTrue(pair.fst().toString().equals(
      "$ [f(x, d(y)) ▷ g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ▷{th} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ▷{select} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ▷{copy} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ▷{lex} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ▷{mul} g(x, x) | y > 0 { y }]\n" +
      "@ [f(x, d(y)) ▷{appl} g(x, x) | y > 0 { y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [f(x, d(y)) ▷ g(x, x) | y > 0 { y }]) or " +
      "[f(x, d(y)) ▷{th} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{select} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{copy} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{lex} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{mul} g(x, x) | y > 0 { y }] or " +
      "[f(x, d(y)) ▷{appl} g(x, x) | y > 0 { y }]\n"));
  }

  @Test
  public void testGeqNoGrTheory() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("y", "Int", "y+x", "Int", "Int",
                                                         "x <= 0", Relation.GEQNOGRTHEORY, "");
    assertTrue(pair.fst().toString().equals(
      "$ [y ≈{theory} y + x | x ≤ 0 { y x }]\n" +
      "@ [y ≽{theory} y + x | x ≤ 0 { y x }]\n" +
      "@ [y ≻{theory} y + x | x ≤ 0 { y x }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "[y ≈{theory} y + x | x ≤ 0 { y x }] == " +
        "([y ≽{theory} y + x | x ≤ 0 { y x }] and " +
        "![y ≻{theory} y + x | x ≤ 0 { y x }])\n"));
  }

  @Test
  public void testSimplifyDistinctTypesAllowed() {
    String trs = "f :: Int -> A g :: Int -> B";
    // you can have different types!
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(x)", "A", "g(x)", "B", "Int",
                                                              "x > 0", Relation.GEQNOGR, trs);
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n(not [f(x) ≈ g(x) | x > 0 { x }]) or " +
      "[f(x) ≈{mono} g(x) | x > 0 { x }] or [f(x) ≈{args} g(x) | x > 0 { x }]\n"));
    pair = setupSimplify("f(x)", "A", "g(x)", "B", "Int", "x > 0", Relation.GEQ, trs);
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n(not [f(x) ≽ g(x) | x > 0 { x }]) or " +
      "[f(x) ≻{rpo} g(x) | x > 0 { x }] or [f(x) ≽{mono} g(x) | x > 0 { x }] or " +
      "[f(x) ≽{args} g(x) | x > 0 { x }]\n"));
    pair = setupSimplify("f(x)", "A", "g(x)", "B", "Int", "x > 0", Relation.GREATER, trs);
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n(not [f(x) ≻ g(x) | x > 0 { x }]) or " +
      "[f(x) ≻{rpo} g(x) | x > 0 { x }] or [f(x) ≻{mono} g(x) | x > 0 { x }] or " +
      "[f(x) ≻{args} g(x) | x > 0 { x }]\n"));
  }

  @Test
  public void testSimplifyDistinctTypeStructureNotAllowed() {
    String trs = "f :: Int -> A g :: Int -> B -> B";
    Pair<HorpoConstraintList,SmtProblem> pair;
    pair = setupSimplify("f(x)", "A", "g(x)", "B -> B", "Int", "x > 0", Relation.GEQNOGR, trs);
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![f(x) ≈ g(x) | x > 0 { x }]\n"));
    pair = setupSimplify("f(x)", "A", "g(x)", "B -> B", "Int", "x > 0", Relation.GEQ, trs);
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![f(x) ≽ g(x) | x > 0 { x }]\n"));
    pair = setupSimplify("f(x)", "A", "g(x)", "B -> B", "Int", "x > 0", Relation.GREATER, trs);
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![f(x) ≻ g(x) | x > 0 { x }]\n"));
  }

  private class FakeSolver implements SmtSolver {
    private ArrayList<String> _requests;
    private boolean[] _answers;
    int _index;
    public FakeSolver(boolean ...answers) {
      _requests = new ArrayList<String>();
      _answers = answers;
      _index = 0;
    }
    // return the next stored answer
    public boolean checkValidity(SmtProblem problem) {
      _requests.add(problem.queryCombinedConstraint().toString());
      return _answers[_index++];
    }
    // this shouldn't be getting called at all
    public SmtSolver.Answer checkSatisfiability(SmtProblem problem) {
      assertTrue(false);
      return null;
    }
  }

  @Test
  public void testGreaterDown() {
    FakeSolver solver = new FakeSolver(true, false);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+1", "Int", "x-1", "Int", "Int",
                                                         "x >= -4", Relation.GREATERTHEORY, "");
    assertTrue(pair.fst().toString().equals("$ [x + 1 ≻{theory} x - 1 | x ≥ -4 { x }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "[x + 1 ≻{theory} x - 1 | x ≥ -4 { x }] == [down]\n"));
    assertTrue(solver._requests.size() == 2);
    assertTrue(solver._requests.get(0).equals(
      "(not (4 + i1 >= 0)) or ((1 + i1 >= i1) and (1001 + i1 >= 0))"));
      // x ≥ -4 ⇒ x + 1 > x - 1 ∧ x + 1 ≥ -1000
    assertTrue(solver._requests.get(1).equals(
      "(not (4 + i1 >= 0)) or ((i1 >= 3 + i1) and (999 >= i1))"));
      // x ≥ -4 ⇒ x + 1 < x - 1 ∧ x + 1 ≤ 1000
  }

  @Test
  public void testGreaterNeither() {
    FakeSolver solver = new FakeSolver(false, false);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+y", "Int", "y", "Int", "Int",
                                                         "x > y", Relation.GREATERTHEORY, "");
    assertTrue(pair.fst().toString().equals("$ [x + y ≻{theory} y | x > y { x y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "![x + y ≻{theory} y | x > y { x y }]\n"));
    assertTrue(solver._requests.size() == 2);
    assertTrue(solver._requests.get(0).equals(
      "(not (i1 >= 1 + i2)) or ((i1 + i2 >= 1 + i2) and (1000 + i1 + i2 >= 0))"));
      // x > y ⇒ x + y > y ∧ x + y ≥ -1000
    assertTrue(solver._requests.get(1).equals(
      "(not (i1 >= 1 + i2)) or ((i2 >= 1 + i1 + i2) and (1000 >= i1 + i2))"));
      // x > y ⇒ x + y < y ∧ x + y ≤ 1000
  }

  @Test
  public void testGeqUp() {
    FakeSolver solver = new FakeSolver(false, true);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+y", "Int", "y", "Int", "Int",
                                                         "x >= 0", Relation.GEQTHEORY, "");
    assertTrue(pair.fst().toString().equals("$ [x + y ≽{theory} y | x ≥ 0 { x y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "[x + y ≽{theory} y | x ≥ 0 { x y }] == ![down]\n"));
    assertTrue(solver._requests.size() == 2);
    assertTrue(solver._requests.get(0).equals(
      "(not (i1 >= 0)) or (i1 + i2 >= i2)"));
      // x ≥ 0 ⇒ x + y ≥ y
    assertTrue(solver._requests.get(1).equals(
      "(not (i1 >= 0)) or (i2 >= i1 + i2)"));
      // x ≥ 0 ⇒ y ≥ x + y
  }

  @Test
  public void testGeqBoth() {
    FakeSolver solver = new FakeSolver(true, true);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+y", "Int", "y", "Int", "Int",
                                                         "x = 0", Relation.GEQTHEORY, "");
    assertTrue(pair.fst().toString().equals("$ [x + y ≽{theory} y | x = 0 { x y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "[x + y ≽{theory} y | x = 0 { x y }]\n"));
    assertTrue(solver._requests.size() == 2);
    assertTrue(solver._requests.get(0).equals(
      "(not (i1 = 0)) or (i1 + i2 >= i2)"));
      // x ≥ 0 ⇒ x + y ≥ y
    assertTrue(solver._requests.get(1).equals(
      "(not (i1 = 0)) or (i2 >= i1 + i2)"));
      // x ≥ 0 ⇒ y ≥ x + y
  }

  @Test
  public void testGreaterWhenNotAllVariablesAreConstrained() {
    FakeSolver solver = new FakeSolver(true, true);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x+y", "Int", "x", "Int", "Int",
                                                         "y = 0", Relation.GEQTHEORY, "");
    assertTrue(pair.fst().toString().equals("$ [x + y ≽{theory} x | y = 0 { y }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "![x + y ≽{theory} x | y = 0 { y }]\n"));
    assertTrue(solver._requests.size() == 0);
  }

  @Test
  public void testBoolComparisonGeqTrue() {
    FakeSolver solver = new FakeSolver(true);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x", "Bool", "x ∧ false", "Bool",
                                                           "Bool", "x", Relation.GEQTHEORY, "");
    assertTrue(pair.fst().toString().equals("$ [x ≽{theory} x ∧ false | x { x }]\n"));
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n[x ≽{theory} x ∧ false | x { x }]\n"));
    assertTrue(solver._requests.size() == 1);
    // x ⇒ x ∨ ¬(x ∧ false)
    assertTrue(solver._requests.get(0).equals("(not b1) or b1 or (not (b1 and false))"));
  }

  @Test
  public void testBoolComparisonGreaterFalse() {
    FakeSolver solver = new FakeSolver(false);
    Settings.smtSolver = solver;
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x", "Bool", "x ∨ false", "Bool",
                                                       "Bool", "x", Relation.GREATERTHEORY, "");
    assertTrue(pair.fst().toString().equals("$ [x ≻{theory} x ∨ false | x { x }]\n"));
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![x ≻{theory} x ∨ false | x { x }]\n"));
    assertTrue(solver._requests.size() == 1);
    // x ⇒ x ∧ ¬(x ∨ false)
    assertTrue(solver._requests.get(0).equals("(not b1) or (b1 and (not (b1 or false)))"));
  }

  @Test
  public void testTheoryComparisonWrongTheoryTypes() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("x", "Bool", "y", "Int", "Int",
                                                              "x", Relation.GREATERTHEORY, "");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![x ≻{theory} y | x { x y }]\n"));
  }

  @Test
  public void testArgs() {
    TRS trs = makeTrs("f :: Int -> A -> A -> Unit\na :: A\nb :: A\n" +
                      "f(x, a, y) -> f(x+1, b, a) | x >= 0");
    // get components for ordering requirements
    HorpoParameters param = new HorpoParameters(1000, false);
    HorpoConstraintList lst = makeList(param, trs);
    Term left = trs.queryRule(0).queryLeftSide();
    Term right = trs.queryRule(0).queryRightSide();
    Term constraint = trs.queryRule(0).queryConstraint();
    TreeSet<Variable> tvar = new TreeSet<Variable>();
    for (Variable x : constraint.vars()) tvar.add(x);

    // store all three kinds of requirements, and handle them
    lst.getVariableFor(left, Relation.GREATERARGS, right, constraint, tvar);
    lst.getVariableFor(left, Relation.GEQNOGRARGS, right, constraint, tvar);
    lst.getVariableFor(left, Relation.GEQARGS, right, constraint, tvar);
    lst.simplify();
    lst.simplify();
    lst.simplify();

    assertTrue(lst.toString().equals(
      "$ [f(x, a, y) ≻{args} f(x + 1, b, a) | x ≥ 0 { x }]\n" +
      "$ [f(x, a, y) ≈{args} f(x + 1, b, a) | x ≥ 0 { x }]\n" +
      "$ [f(x, a, y) ≽{args} f(x + 1, b, a) | x ≥ 0 { x }]\n" +
      "@ [x ≽ x + 1 | x ≥ 0 { x }]\n" +
      "@ [a ≽ b | x ≥ 0 { }]\n" +
      "@ [y ≽ a | x ≥ 0 { }]\n" +
      "@ [x ≻ x + 1 | x ≥ 0 { x }]\n" +
      "@ [a ≻ b | x ≥ 0 { }]\n" +
      "@ [y ≻ a | x ≥ 0 { }]\n" +
      "@ [x ≈ x + 1 | x ≥ 0 { x }]\n" +
      "@ [a ≈ b | x ≥ 0 { }]\n" +
      "@ [y ≈ a | x ≥ 0 { }]\n"));

    assertTrue(param.queryProblem().toString().equals(
      "[alwaystrue]\n" +
      "(not [f(x, a, y) ≻{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,1)] or [x ≽ x + 1 | x ≥ 0 { x }]\n" +
      "(not [f(x, a, y) ≻{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,2)] or [a ≽ b | x ≥ 0 { }]\n" +
      "(not [f(x, a, y) ≻{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,3)] or [y ≽ a | x ≥ 0 { }]\n" +
      "(not [f(x, a, y) ≻{args} f(x + 1, b, a) | x ≥ 0 { x }]) or " +
        "([regards(f,1)] and [x ≻ x + 1 | x ≥ 0 { x }]) or " +
        "([regards(f,2)] and [a ≻ b | x ≥ 0 { }]) or " +
        "([regards(f,3)] and [y ≻ a | x ≥ 0 { }])\n" +
      "(not [f(x, a, y) ≈{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,1)] or [x ≈ x + 1 | x ≥ 0 { x }]\n" +
      "(not [f(x, a, y) ≈{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,2)] or [a ≈ b | x ≥ 0 { }]\n" +
      "(not [f(x, a, y) ≈{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,3)] or [y ≈ a | x ≥ 0 { }]\n" +
      "(not [f(x, a, y) ≽{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,1)] or [x ≽ x + 1 | x ≥ 0 { x }]\n" +
      "(not [f(x, a, y) ≽{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,2)] or [a ≽ b | x ≥ 0 { }]\n" +
      "(not [f(x, a, y) ≽{args} f(x + 1, b, a) | x ≥ 0 { x }]) or ![regards(f,3)] or [y ≽ a | x ≥ 0 { }]\n"));
  }

  @Test
  public void testMono() {
    TRS trs = makeTrs("Q :: A -> A\na :: A\nb :: A\nc :: Int -> A" +
                      "{ F :: A -> A -> A } Q(F(c(x), a)) -> Q(F(b, c(x))) | x = 0");
    // get components for ordering requirements
    HorpoParameters param = new HorpoParameters(1000, false);
    HorpoConstraintList lst = makeList(param, trs);
    Term left = trs.queryRule(0).queryLeftSide().queryArgument(1);
    Term right = trs.queryRule(0).queryRightSide().queryArgument(1);
    Term constraint = trs.queryRule(0).queryConstraint();
    TreeSet<Variable> tvar = new TreeSet<Variable>();
    for (Variable x : constraint.vars()) tvar.add(x);

    // store all three kinds of requirements, and handle them
    lst.getVariableFor(left, Relation.GREATERMONO, right, constraint, tvar);
    lst.getVariableFor(left, Relation.GEQNOGRMONO, right, constraint, tvar);
    lst.getVariableFor(left, Relation.GEQMONO, right, constraint, tvar);
    lst.simplify();
    lst.simplify();
    lst.simplify();

    assertTrue(lst.toString().equals(
      "$ [F(c(x), a) ≻{mono} F(b, c(x)) | x = 0 { x }]\n" +
      "$ [F(c(x), a) ≈{mono} F(b, c(x)) | x = 0 { x }]\n" +
      "$ [F(c(x), a) ≽{mono} F(b, c(x)) | x = 0 { x }]\n" +
      "@ [c(x) ≈ b | x = 0 { x }]\n" +
      "@ [a ≈ c(x) | x = 0 { x }]\n" +
      "@ [c(x) ≽ b | x = 0 { x }]\n" +
      "@ [a ≽ c(x) | x = 0 { x }]\n"));

    assertTrue(param.queryProblem().toString().equals(
      "[alwaystrue]\n" +
      "![F(c(x), a) ≻{mono} F(b, c(x)) | x = 0 { x }]\n" +
      "(not [F(c(x), a) ≈{mono} F(b, c(x)) | x = 0 { x }]) or [c(x) ≈ b | x = 0 { x }]\n" +
      "(not [F(c(x), a) ≈{mono} F(b, c(x)) | x = 0 { x }]) or [a ≈ c(x) | x = 0 { x }]\n" +
      "(not [F(c(x), a) ≽{mono} F(b, c(x)) | x = 0 { x }]) or [c(x) ≽ b | x = 0 { x }]\n" +
      "(not [F(c(x), a) ≽{mono} F(b, c(x)) | x = 0 { x }]) or [a ≽ c(x) | x = 0 { x }]\n"));
  }

  @Test
  public void testEquality() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f", "A -> A", "f", "A -> A", "Int",
                                                         "true", Relation.GEQEQUAL, "f :: A -> A");
    assertTrue(pair.fst().toString().equals("$ [f ≽{equal} f | true { }]\n"));
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n[f ≽{equal} f | true { }]\n"));

    HorpoParameters param = new HorpoParameters(1000, true);
    HorpoConstraintList lst = makeList(param, makeTrs(""));
    Term x = TermFactory.createVar("x");
    lst.getVariableFor(x, Relation.GEQNOGREQUAL, x, TheoryFactory.createValue(true),
                       new TreeSet<Variable>());
    lst.simplify();
    assertTrue(lst.toString().equals("$ [x ≈{equal} x | true { }]\n"));
    assertTrue(param.queryProblem().toString().equals("[alwaystrue]\n[x ≈{equal} x | true { }]\n"));
  }

  @Test
  public void testMonoWithDistinctHeadSymbols() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(1)", "Int", "g(2)", "Int", "Int",
                                 "true", Relation.GREATERMONO, "f :: Int -> Int g :: Int -> Int");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![f(1) ≻{mono} g(2) | true { }]\n"));
  }

  @Test
  public void testGreaterRpo() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(1)", "Int", "g(2)", "Int", "Int",
                                  "true", Relation.GREATERRPO, "f :: Int -> Int g :: Int -> Int");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n" +
      "(not [f(1) ≻{rpo} g(2) | true { }]) or [f(1) ▷ g(2) | true { }]\n"));
    pair = setupSimplify("f(1)", "Int -> Int -> Int", "3", "Int", "Int", "true",
                         Relation.GREATERRPO, "f :: Int -> Int -> Int -> Int");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n" +
      "(not [f(1) ≻{rpo} 3 | true { }]) or [regards(f,2)]\n" +
      "(not [f(1) ≻{rpo} 3 | true { }]) or [regards(f,3)]\n" +
      "(not [f(1) ≻{rpo} 3 | true { }]) or [f(1) ▷ 3 | true { }]\n"));
    pair = setupSimplify("x + 3", "Int", "x", "Int", "Int", "x > 0", Relation.GREATERRPO, "");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![x + 3 ≻{rpo} x | x > 0 { x }]\n"));
  }

  @Test
  public void testRpoTheory() {
    // values
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("a", "Int", "true", "Bool", "Int",
                                                         "true", Relation.RPOTH, "a :: Int");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n[a ▷{th} true | true { }]\n"));
    // complex expressions with variable in theory
    pair = setupSimplify("a", "A", "x + y/2", "Int", "Int", "x > 0", Relation.RPOTH, "a :: A");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n" +
      "[a ▷{th} x + y / 2 | x > 0 { x y }]\n"));
    // non-example: a variable that is not in the theory
    pair = setupSimplify("a", "A", "x", "Int", "Int", "y > 0", Relation.RPOTH, "a :: A");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![a ▷{th} x | y > 0 { }]\n"));
  }

  @Test
  public void testAppl() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("a", "Int", "f(1,2,g(3))", "Int",
              "Int", "true", Relation.RPOAPPL, "f :: Int -> Int -> Int -> Int g :: Int -> Int");
    assertTrue(pair.fst().toString().equals(
      "$ [a ▷{appl} f(1, 2, g(3)) | true { }]\n" +
      "@ [a ▷ f(1, 2) | true { }]\n" +
      "@ [a ▷ g(3) | true { }]\n"));
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [a ▷{appl} f(1, 2, g(3)) | true { }]) or [a ▷ f(1, 2) | true { }]\n" +
      "(not [a ▷{appl} f(1, 2, g(3)) | true { }]) or [a ▷ g(3) | true { }]\n"));
  }

  @Test
  public void testRpoSelect() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(x,a,y)", "Unit", "a", "A", "Int",
      "true", Relation.RPOSELECT, "f :: (Int -> Bool) -> A -> Int -> Unit\na :: A");
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "(not [f(x, a, y) ▷{select} a | true { y }]) or " +
      "([regards(f,1)] and [x ≽ a | true { }]) or " +
      "([regards(f,2)] and [a ≽ a | true { }]) or " +
      "([regards(f,3)] and [y ≽ a | true { y }])\n"));
  }

  @Test
  public void testCopy() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(a)", "Int", "g(b,x)", "Int", "Int",
              "true", Relation.RPOCOPY, "f :: Int -> Int g :: Int -> Int -> Int a :: Int b :: Int");
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "[pred(f)] >= 0\n" +
      "[pred(g)] >= 0\n" +
      "(not [f(a) ▷{copy} g(b, x) | true { }]) or ([pred(f)] >= 1 + [pred(g)])\n" +
      "(not [f(a) ▷{copy} g(b, x) | true { }]) or ![regards(g,1)] or [f(a) ▷ b | true { }]\n" +
      "(not [f(a) ▷{copy} g(b, x) | true { }]) or ![regards(g,2)] or [f(a) ▷ x | true { }]\n"));
  }

  @Test
  public void testFailedCopy() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(a)", "Int", "f(b)", "Int", "Int",
                                   "true", Relation.RPOCOPY, "f :: Int -> Int a :: Int b :: Int");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![f(a) ▷{copy} f(b) | true { }]\n"));
  }

  @Test
  public void testFailedLex() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(F,x)", "A", "F(x)", "A", "Int",
                                       "x > 0", Relation.RPOLEX, "f :: (Int -> A) -> Int -> A");
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n![f(F, x) ▷{lex} F(x) | x > 0 { x }]\n"));
  }

  @Test
  public void testLexWithZeroArguments() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f", "Int -> B", "f(0)" ,"B", "Int",
                                                        "true", Relation.RPOLEX, "f :: Int -> B");
    assertTrue(pair.snd().toString().equals("[alwaystrue]\n![f ▷{lex} f(0) | true { }]\n"));
  }

  @Test
  public void testLexWithOneArgument() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(x,y)", "A", "g(y)" ,"B", "Int",
                                 "true", Relation.RPOLEX, "f :: Int -> Int -> A g :: Int -> B");
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      "[pred(f)] >= 0\n" +
      "[pred(g)] >= 0\n" +
      "(not [f(x, y) ▷{lex} g(y) | true { y }]) or ([pred(f)] = [pred(g)])\n" + // same precedence
      "[stat(f)] >= 1\n" +
      "2 >= [stat(f)]\n" +
      "(not [f(x, y) ▷{lex} g(y) | true { y }]) or ([stat(f)] = 1)\n" + // stat(f) = Lex
      "(not [f(x, y) ▷{lex} g(y) | true { y }]) or (0 = 0)\n" +         // stat(g) = Lex
      "(not [f(x, y) ▷{lex} g(y) | true { y }]) or [regards(f,1)]\n" +  // first arg of f regarded
      "(not [f(x, y) ▷{lex} g(y) | true { y }]) or [regards(g,1)]\n" +  // first arg of g regarded
      "(not [f(x, y) ▷{lex} g(y) | true { y }]) or [x ≻ y | true { y }]\n")); // argument decreases
  }

  @Test
  public void testLexWithMultipleArguments() {
    Pair<HorpoConstraintList,SmtProblem> pair = setupSimplify("f(a,b,c)", "A", "g(u,v,w,x)" ,"A",
             "Int", "true", Relation.RPOLEX, "f :: B -> B -> B -> A g :: B -> B -> B -> B -> A");
    assertTrue(pair.snd().toString().equals(
      "[alwaystrue]\n" +
      // they have the same precedence
      "[pred(f)] >= 0\n" +
      "[pred(g)] >= 0\n" +
      "(not [f(a, b, c) ▷{lex} g(u, v, w, x) | true { }]) or ([pred(f)] = [pred(g)])\n" +
      // they both have status lex
      "[stat(f)] >= 1\n" +
      "3 >= [stat(f)]\n" +
      "(not [f(a, b, c) ▷{lex} g(u, v, w, x) | true { }]) or ([stat(f)] = 1)\n" +
      "[stat(g)] >= 1\n" +
      "4 >= [stat(g)]\n" +
      "(not [f(a, b, c) ▷{lex} g(u, v, w, x) | true { }]) or ([stat(g)] = 1)\n" +
      // index ∈ {1,..3}
      "i5 >= 1\n" +
      "3 >= i5\n" +
      // for i ∈ {1..2}: if i < index then:
      //   * ¬regards(f,i) ⇒ ¬regards(g,i)
      //   * regards(f,i) ⇒ regards(g,i)
      //   * regards(f,i) ⇒ leftarg[i] ≈ rightarg[i]
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (1 >= i5) or [regards(f,1)] or ![regards(g,1)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (1 >= i5) or ![regards(f,1)] or [regards(g,1)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (1 >= i5) or ![regards(f,1)] or [a ≈ u | true { }]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (2 >= i5) or [regards(f,2)] or ![regards(g,2)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (2 >= i5) or ![regards(f,2)] or [regards(g,2)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (2 >= i5) or ![regards(f,2)] or [b ≈ v | true { }]\n" +
      // for i ∈ {1..3}: if i = index then:
      //   * regards(f,i)
      //   * regards(g,i)
      //   * leftarg[i] ≻ rightarg[i]
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (1 # i5) or [regards(f,1)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (1 # i5) or [regards(g,1)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (1 # i5) or [a ≻ u | true { }]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (2 # i5) or [regards(f,2)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (2 # i5) or [regards(g,2)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (2 # i5) or [b ≻ v | true { }]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (3 # i5) or [regards(f,3)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (3 # i5) or [regards(g,3)]\n" +
      "![f(a, b, c) ▷{lex} g(u, v, w, x) | true { }] or (3 # i5) or [c ≻ w | true { }]\n" +
      // left ▷ each right argument that is regarded (not including the first, because that one's covered)
      "(not [f(a, b, c) ▷{lex} g(u, v, w, x) | true { }]) or ![regards(g,2)] or [f(a, b, c) ▷ v | true { }]\n" +
      "(not [f(a, b, c) ▷{lex} g(u, v, w, x) | true { }]) or ![regards(g,3)] or [f(a, b, c) ▷ w | true { }]\n" +
      "(not [f(a, b, c) ▷{lex} g(u, v, w, x) | true { }]) or ![regards(g,4)] or [f(a, b, c) ▷ x | true { }]\n" ));
  }
}

