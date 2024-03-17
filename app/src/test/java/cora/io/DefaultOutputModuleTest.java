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

import cora.utils.Pair;
import cora.terms.Term;
import cora.terms.TermPrinter.Renaming;
import cora.trs.Rule;
import cora.trs.TRS;
import cora.reader.CoraInputReader;

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
    assertTrue(o.toString().equals("  ABCD x\n  \n  E\n\nSome more testing\n\n"));
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
    o.println("a %s bing%a %{lambda} %% %s gg!", "hel%slo", "test?");
    assertTrue(o.toString().equals("a hel%slo bing%a \\ % test? gg!\n\n"));
  }

  @Test
  public void testPrintTermsWithDistinctVariablesWithoutRenaming() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    Term a = CoraInputReader.readTerm("f(x, 3)", trs);
    Term b = CoraInputReader.readTerm("f(0, x + y)", trs);
    o.println("First attempt: terms are %t and %t.", a, b);
    o.print("Second attempt: terms are %t", a);
    o.print(" and %t.", b);
    assertTrue(o.toString().equals(
      "First attempt: terms are f(x__1, 3) and f(0, x__2 + y).\n\n" +
      "Second attempt: terms are f(x, 3) and f(0, x + y).\n\n"));
  }

  @Test
  public void testPrintTermsWithRenaming() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    Term extra = CoraInputReader.readTerm("f(x, 3)", trs);
    Term a = CoraInputReader.readTerm("f(x, y)", trs);
    Term b = CoraInputReader.readTerm("f(x, y)", trs);
    Renaming renaming = o.queryTermPrinter().generateUniqueNaming(extra, a);
    o.println("First attempt: %t, %t.", a, b);
    o.println("Second attempt: %t, %t.", new Pair<Term,Renaming>(a,renaming), b);
    assertTrue(o.toString().equals("First attempt: f(x__1, y__1), f(x__2, y__2).\n\n" +
                                   "Second attempt: f(x__2, y), f(x, y).\n\n"));
  }

  @Test
  public void testPrintRule() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    Rule r1 = trs.queryRule(0);
    Rule r2 = trs.queryRule(1);
    o.println("Rule %r, rule %r, lhs %t, lhs %t.", r1, r2, r1.queryLeftSide(), r2.queryLeftSide());
    assertTrue(o.toString().equals("Rule f(x, y) -> f(y, x) | x > y, rule a(x) -> 3, " +
                                   "lhs f(x__1, y), lhs a(x__2).\n\n"));
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
    o.println("Test 1: %s, %s, %s", "a", "b");
    assertTrue(o.toString().equals("Test 1: a, b, %s\n\n"));
    assertThrows(IllegalPrintError.class, () -> o.print("Test 2: %s, %s", "a", "b", "c"));
  }

  @Test
  public void testPrintIllegalType() {
    TRS trs = exampleTrs();
    OutputModule o = DefaultOutputModule.createPlainModule(trs);
    assertThrows(IllegalPrintError.class, () -> o.println("%s", 3));
    assertThrows(IllegalPrintError.class, () -> o.println("%t", "string"));
    assertThrows(IllegalPrintError.class, () -> o.println("%r", "string"));
  }
}

