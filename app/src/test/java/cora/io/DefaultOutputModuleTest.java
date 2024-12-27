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

package cora.io;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.List;
import java.util.Set;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.trs.*;
import charlie.reader.CoraInputReader;

public class DefaultOutputModuleTest {
  private TRS exampleTrs() {
    return CoraInputReader.readTrsFromString("f :: Int -> Int -> Int\na::Int -> Int\n" +
                                             "f(x,y) -> f(y,x) | x> y\n" +
                                             "a(x) -> 3");
  }

  @Test
  public void testPrintTwoParagraphs() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.print("Hello ");
    o.println("world!");
    o.print("Test.");
    o.println();
    assertTrue(o.toString().equals("Hello world!\n\nTest.\n\n"));
  }

  @Test
  public void testPrintEmptyParagraph() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.println();
    o.println("Beep!");
    o.println();
    o.println("Boop!");
    assertTrue(o.toString().equals("\nBeep!\n\n\nBoop!\n\n"));
  }

  @Test
  public void testPrintSimpleTable() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.startTable();
    o.print("A");
    o.nextColumn();
    o.print("B");
    o.println();
    o.nextColumn("C");
    o.nextColumn("D");
    o.endTable();
    assertTrue(o.toString().equals("  A B\n  C D\n\n"));
  }

  @Test
  public void testPadding() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.startTable();
    o.nextColumn("Hello");
    o.nextColumn("a");
    o.println();
    o.nextColumn("bb");
    o.print("Super long");
    o.println(" line!");
    o.endTable();
    assertTrue(o.toString().equals("  Hello a\n  bb    Super long line!\n\n"));
  }

  @Test
  public void testEmptyTable() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.startTable();
    o.endTable();
    assertTrue(o.toString().equals("\n"));
  }

  @Test
  public void testAlmostEmptyTable() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.startTable();
    o.println();
    o.endTable();
    assertTrue(o.toString().equals("  \n\n"));
  }

  @Test
  public void testTableAndParagraph() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.startTable();
    o.nextColumn("ABCD");
    o.println("x");
    o.println();
    o.println("E");
    o.endTable();
    o.print("Some more testing");
    assertTrue(o.toString().equals("  ABCD x\n  \n  E\n\nSome more testing"));
  }

  @Test
  public void testParagraphAndTable() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.println("Hello");
    o.startTable();
    o.println("bing");
    o.endTable();
    o.println("Bye.");
    assertTrue(o.toString().equals("Hello\n\n  bing\n\nBye.\n\n"));
  }

  @Test
  public void testCodes() {
    OutputModule p = DefaultOutputModule.createPlainModule(exampleTrs());
    p.println("%{ruleArrow}, %{typeArrow}, %{lambda}, %{vdash}");
    assertTrue(p.toString().equals("->, ->, \\, |-\n\n"));
    OutputModule u = DefaultOutputModule.createUnicodeModule(exampleTrs());
    u.println("%{ruleArrow}, %{typeArrow}, %{lambda}, %{vdash}");
    assertTrue(u.toString().equals("→, →, λ, ⊢\n\n"));
  }

  @Test
  public void testTermWithStringCodes() {
    OutputModule o = DefaultOutputModule.createPlainModule(exampleTrs());
    o.println("a %a bing%s %{lambda} %% %a gg!", "hel%alo", "test?");
    assertTrue(o.toString().equals("a hel%alo bing%s \\ %% test? gg!\n\n"));
  }

  @Test
  public void testPrintTermsWithDistinctVariablesWithoutRenaming() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    Term a = CoraInputReader.readTerm("f(x, 3)", trs);
    Term b = CoraInputReader.readTerm("f(0, x + y)", trs);
    o.println("First attempt: terms are %a and %a.", a, b);
    o.print("Second attempt: terms are %a", a);
    o.print(" and %a.", b);
    assertTrue(o.toString().equals(
      "First attempt: terms are f(x__1, 3) and f(0, x__2 + y).\n\n" +
      "Second attempt: terms are f(x, 3) and f(0, x + y)."));
  }

  @Test
  public void testPrintTermsWithRenaming() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    Term extra = CoraInputReader.readTerm("f(x, 3)", trs);
    Term a = CoraInputReader.readTerm("f(x, y)", trs);
    Term b = CoraInputReader.readTerm("f(x, y)", trs);
    Renaming renaming = o.queryTermPrinter().generateUniqueNaming(extra, a);
    o.println("First attempt: %a, %a.", a, b);
    o.println("Second attempt: %a, %a.", new Pair<Term,Renaming>(a,renaming), b);
    assertTrue(o.toString().equals("First attempt: f(x__1, y__1), f(x__2, y__2).\n\n" +
                                   "Second attempt: f(x__2, y), f(x, y).\n\n"));
  }

  @Test
  public void testPrintType() {
    TRS trs = exampleTrs();
    Type t = CoraInputReader.readType("(a -> b) -> (c -> d)");
    OutputModule p = DefaultOutputModule.createPlainModule(trs);
    OutputModule u = DefaultOutputModule.createUnicodeModule(trs);
    p.println("%a", t);
    u.println("%a", t);
    assertTrue(p.toString().equals("(a -> b) -> c -> d\n\n"));
    assertTrue(u.toString().equals("(a → b) → c → d\n\n"));
  }

  @Test
  public void testPrintPosition() throws charlie.exceptions.CustomParserException {
    OutputModule p = DefaultOutputModule.createPlainModule();
    OutputModule u = DefaultOutputModule.createUnicodeModule();
    Position pos = Position.parse("1.2.☆3");
    p.println("%a", pos);
    u.println("%a", pos);
    assertTrue(p.toString().equals("1.2.*3\n\n"));
    assertTrue(u.toString().equals("1.2.☆3\n\n"));
  }

  @Test
  public void testPrintRule() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    Rule r1 = trs.queryRule(0);
    Rule r2 = trs.queryRule(1);
    o.println("Rule %a, rule %a, lhs %a, lhs %a.", r1, r2, r1.queryLeftSide(), r2.queryLeftSide());
    assertTrue(o.toString().equals("Rule f(x, y) -> f(y, x) | x > y, rule a(x) -> 3, " +
                                   "lhs f(x__1, y), lhs a(x__2).\n\n"));
  }

  @Test
  public void testObjectPair() {
    Term x = TermFactory.createVar("x");
    Term y = TermFactory.createVar("x");
    Term z = TermFactory.createVar("x");
    Object first = new Pair<String,Object[]>("(%a,%a)", new Object[] {y, x});
    Object second = new Pair<String,Object[]>("we have: %a and %a.", new Object[] {z, first});
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    o.println("[%a]", second);
    assertTrue(o.toString().equals("[we have: x and (x__2,x__1).]\n\n"));
  }

  @Test
  public void testErrorsWhenNotInATable() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    o.print("Hello");
    assertThrows(IllegalPrintError.class, () -> o.endTable());
    assertThrows(IllegalPrintError.class, () -> o.nextColumn());
    o.startTable();
    o.print("Ping");
    o.startTable();
    o.print("Pong");
    o.endTable();
    assertTrue(o.toString().equals("Hello\n\n  Ping\n\n  Pong\n\n"));
  }

  @Test
  public void testIncorrectNumberOfArguments() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    o.println("Test 1: %a, %a, %a", "a", "b");
    assertTrue(o.toString().equals("Test 1: a, b, %a\n\n"));
    assertThrows(IllegalPrintError.class, () -> o.print("Test 2: %a, %a", "a", "b", "c"));
  }

  @Test
  public void testPrintTrs() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createUnicodeModule(trs);
    o.printTrs(trs);
    assertTrue(o.toString().equals(
      "Cora-TRS with rule schemes Beta and Calc:\n\n" +
      "  Signature: a :: Int → Int\n" +
      "             f :: Int → Int → Int\n\n" +
      "  Rules: f(x, y) → f(y, x) | x > y\n" +
      "         a(x) → 3\n\n"));
  }

  @Test
  public void testPrintEmptyTrs() {
    TRS trs = TrsFactory.createTrs(new Alphabet(List.of()), List.of(), TrsFactory.AMS);
    OutputModule o = DefaultOutputModule.createUnicodeModule(trs);
    o.printTrs(trs);
    assertTrue(o.toString().equals(
      "AMS with only rule scheme Beta:\n\n" +
      "  Signature: (empty)\n\n" +
      "  Rules: (empty)\n\n"));
  }

  @Test
  public void testPrintSubstitutionWithOneRenaming() {
    Type itype = CoraInputReader.readType("Int");
    Variable x = TermFactory.createVar("x", itype);
    Variable y = TermFactory.createVar("x", itype);
    Variable z = TermFactory.createBinder("x", itype);
    MetaVariable zz = TermFactory.createMetaVar("Z", CoraInputReader.readType("Int -> Int"), 1);
    Term zz0 = TermFactory.createMeta(zz, TheoryFactory.createValue(0));
    TRS trs = exampleTrs();
    Term faxy = trs.lookupSymbol("f").apply(trs.lookupSymbol("a").apply(x)).apply(y);
    Term lfzx = TermFactory.createAbstraction(z, trs.lookupSymbol("f").apply(z).apply(x));
    Renaming renaming = (new TermPrinter(Set.of())).generateUniqueNaming(faxy, lfzx, zz0);

    // []
    Substitution gamma = TermFactory.createEmptySubstitution();
    OutputModule o = DefaultOutputModule.createUnicodeModule(trs);
    o.println("%a", new Pair<Substitution,Renaming>(gamma, renaming));
    assertTrue(o.toString().equals("[]\n\n"));

    // [x := f(a(x),y)]
    gamma.extend(x, faxy);
    o.println("%a", new Pair<Substitution,Renaming>(gamma, renaming));

    // [x := f(a(x), y); Z := λz.f(z,x)]
    gamma.extend(zz, lfzx);
    o.println("%a", new Pair<Substitution,Renaming>(gamma, renaming));

    assertTrue(o.toString().equals("[]\n\n" +
      "[x__1 := f(a(x__1), x__2)]\n\n" +
      "[Z := λx1.f(x1, x__1); x__1 := f(a(x__1), x__2)]\n\n"));
  }

  @Test
  public void testPrintSubstitutionWithTwoRenamings() {
    Type itype = CoraInputReader.readType("Int");
    Variable x = TermFactory.createVar("x", itype);
    Variable y = TermFactory.createVar("x", itype);
    Variable z = TermFactory.createBinder("z", itype);
    MetaVariable zz = TermFactory.createMetaVar("Z", CoraInputReader.readType("Int -> Int"), 1);
    Term zz0 = TermFactory.createMeta(zz, TheoryFactory.createValue(0));
    TRS trs = exampleTrs();
    Term faxy = trs.lookupSymbol("f").apply(trs.lookupSymbol("a").apply(x)).apply(y);
    Term lfzx = TermFactory.createAbstraction(z, trs.lookupSymbol("f").apply(z).apply(x));

    TermPrinter tmp = new TermPrinter(Set.of());
    Renaming keys = tmp.generateUniqueNaming(x, zz0);
    Renaming values = tmp.generateUniqueNaming(faxy, lfzx);

    Substitution gamma = TermFactory.createEmptySubstitution();
    Pair<Substitution,Pair<Renaming,Renaming>> p =  new Pair<Substitution,Pair<Renaming,Renaming>>(
      gamma,new Pair<Renaming,Renaming>(keys, values));

    // []
    OutputModule o = DefaultOutputModule.createUnicodeModule(trs);
    o.println("%a", p);
    assertTrue(o.toString().equals("[]\n\n"));

    // [x := f(a(x),y)]
    gamma.extend(x, faxy);
    o.println("%a", p);

    // [x := f(a(x), y); Z := λz.f(z,x)]
    gamma.extend(zz, lfzx);
    o.println("%a", p);

    assertTrue(o.toString().equals("[]\n\n" +
        "[x := f(a(x__1), x__2)]\n\n" +
        "[Z := λz.f(z, x__1); x := f(a(x__1), x__2)]\n\n"));
  }

  @Test
  public void testMissingKeyInSubstitutionPrint() {
    Substitution gamma = TermFactory.createEmptySubstitution();
    TRS trs = exampleTrs();
    Term fx3 = CoraInputReader.readTerm("f(x, 3)", trs);
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(TermFactory.createVar("x", CoraInputReader.readType("Int")), fx3);
    Renaming renaming = (new TermPrinter(Set.of())).generateUniqueNaming(fx3);
    OutputModule o = DefaultOutputModule.createUnicodeModule(trs);
    assertThrows(IllegalArgumentException.class, () ->
      o.println("%a", new Pair<Substitution,Renaming>(subst, renaming)));
  }
}

