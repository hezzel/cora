/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.printer;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;

import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TypePrinter;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import charlie.reader.CoraInputReader;

/** Testing the two string comparison constraints */
public class PrinterTest {
  private Type type(String txt) {
    return CoraInputReader.readType(txt);
  }

  private TRS exampleTrs() {
    return CoraInputReader.readTrsFromString("f :: Int -> Int -> Int\na::Int -> Int\n" +
                                             "f(x,y) -> f(y,x) | x> y\n" +
                                             "a(x) -> 3");
  }

  @Test
  public void testBasics() throws Exception {
    TRS trs = exampleTrs();
    Printer printer = PrinterFactory.createUnicodePrinter(trs);
    Term term = CoraInputReader.readTerm("f(a(3), y)", trs);
    Position position = Position.parse("0.-3.*1");
    printer.add("Hello world.\n");
    printer.add("This is a type: " + trs.lookupSymbol("f").queryType());
    printer.add("This ", "is ", "a term: ", term, ".\n");
    printer.add("This is a position: ", position, ".\n");
    printer.add("No problem with integers (", 17, ") either!\n");
    assertTrue(printer.toString().equals(
      "Hello world.\n" +
      "This is a type: Int → Int → IntThis is a term: f(a(3), y).\n" +
      "This is a position: 0.!3.☆1.\n" +
      "No problem with integers (17) either!\n"));
  }

  @Test
  public void testSymbols() {
    TRS trs = exampleTrs();
    Printer upr = PrinterFactory.createUnicodePrinter(trs);
    upr.add(upr.symbRuleArrow(), upr.symbLambda(), upr.symbBullet(), upr.symbForall());
    assertTrue(upr.toString().equals("→λ•∀"));
    Printer apr = PrinterFactory.createPlainPrinter(trs);
    apr.add(apr.symbRuleArrow(), apr.symbLambda(), apr.symbBullet(), apr.symbForall());
    assertTrue(apr.toString().equals("->lambda#FORALL "));
  }

  @Test
  public void testPrintTermsWithDistinctVariablesWithoutRenaming() {
    TRS trs = exampleTrs();
    Printer printer = PrinterFactory.createUnicodePrinter(trs);
    Term a = CoraInputReader.readTerm("f(x, 3)", trs);
    Term b = CoraInputReader.readTerm("f(0, x + y)", trs);
    printer.add("First attempt: terms are ", a, " and ", b, ".\n");
    printer.add("Second attempt: terms are ", a);
    printer.add(" and ", b, ".");
    assertTrue(printer.toString().equals(
      "First attempt: terms are f(x__1, 3) and f(0, x__2 + y).\n" +
      "Second attempt: terms are f(x, 3) and f(0, x + y)."));
  }

  @Test
  public void testPrintTermsWithRenaming() {
    TRS trs = exampleTrs();
    Printer printer = PrinterFactory.createUnicodePrinter(trs);
    Term extra = CoraInputReader.readTerm("f(x, 3)", trs);
    Term a = CoraInputReader.readTerm("f(x, y)", trs);
    Term b = CoraInputReader.readTerm("f(x, y)", trs);
    Renaming renaming = printer.generateUniqueNaming(extra, a);
    printer.add("First attempt: ", a, ", ", b, ".\n");
    printer.add("Second attempt: ", new Pair<Term,Renaming>(a,renaming), ", ", b, ".\n");
    assertTrue(printer.toString().equals("First attempt: f(x__1, y__1), f(x__2, y__2).\n" +
                                         "Second attempt: f(x__2, y), f(x, y).\n"));
  }

  @Test
  public void testPrintObjectList() {
    TRS trs = exampleTrs();
    Variable x = TermFactory.createVar("x");
    Variable y = TermFactory.createVar("x");
    Variable z = TermFactory.createVar("x");
    Variable u = TermFactory.createVar("x");
    Printer printer = PrinterFactory.createPlainPrinter(trs);
    printer.add(new Object[] { "x = ", x, " and y = ", y },
      List.of(" and z = ", z, " and u = ", u));
    assertTrue(printer.toString().equals("x = x__1 and y = x__2 and z = x__1 and u = x__2"));
  }

  @Test
  public void testParseableRule() {
    // f(x,a) -> f(y,λb.G[b]) | x > z ∧ z > y
    Term f = TermFactory.createConstant("f", type("Int → (Int → Int) → Int"));
    Variable x = TermFactory.createVar("x", type("Int"));
    Variable y = TermFactory.createVar("y", type("Int"));
    Variable z = TermFactory.createVar("y", type("Int"));
    Variable a = TermFactory.createVar("a", type("Int → Int"));
    Variable b = TermFactory.createBinder("b", type("Int"));
    MetaVariable g = TermFactory.createMetaVar("G", type("Int"), type("Int"));
    Term bgb = TermFactory.createAbstraction(b, TermFactory.createMeta(g, b));
    Term l = f.apply(x).apply(a);
    Term r = f.apply(y).apply(bgb);
    Term xz = TheoryFactory.greaterSymbol.apply(x).apply(z);
    Term zy = TheoryFactory.greaterSymbol.apply(z).apply(y);
    Term c = TheoryFactory.createConjunction(xz, zy);
    Rule rule = TrsFactory.createRule(l, r, c);
    // do the printing!
    Printer pr = PrinterFactory.createParseablePrinter(exampleTrs());
    pr.add(rule);
    assertTrue(pr.toString().equals("{ G :: [Int] -> Int, x :: Int, y__1 :: Int, y__2 :: Int, " +
      "a__1 :: Int -> Int } f(x, a__1) -> f(y__1, \\b :: Int.G[b]) | x > y__2 /\\ y__2 > y__1"));
  }

  @Test
  public void testPrintSubstitutionWithOneRenaming() {
    TRS trs = exampleTrs();
    Printer printer = PrinterFactory.createUnicodePrinter(trs);

    Type itype = CoraInputReader.readType("Int");
    Variable x = TermFactory.createVar("x", itype);
    Variable y = TermFactory.createVar("x", itype);
    Variable z = TermFactory.createBinder("x", itype);
    MetaVariable zz = TermFactory.createMetaVar("Z", CoraInputReader.readType("Int -> Int"), 1);
    Term zz0 = TermFactory.createMeta(zz, TheoryFactory.createValue(0));
    Term faxy = trs.lookupSymbol("f").apply(trs.lookupSymbol("a").apply(x)).apply(y);
    Term lfzx = TermFactory.createAbstraction(z, trs.lookupSymbol("f").apply(z).apply(x));
    Renaming renaming = printer.generateUniqueNaming(faxy, lfzx, zz0);

    // []
    Substitution gamma = TermFactory.createEmptySubstitution();
    printer.add(new Pair<Substitution,Renaming>(gamma, renaming));
    printer.add("\n");
    assertTrue(printer.toString().equals("[]\n"));

    // [x := f(a(x),y)]
    gamma.extend(x, faxy);
    printer.add(new Pair<Substitution,Renaming>(gamma, renaming));
    printer.add("\n");

    // [x := f(a(x), y); Z := λz.f(z,x)]
    gamma.extend(zz, lfzx);
    printer.add(new Pair<Substitution,Renaming>(gamma, renaming));

    assertTrue(printer.toString().equals("[]\n" +
      "[x__1 := f(a(x__1), x__2)]\n" +
      "[x__1 := f(a(x__1), x__2), Z := λx1.f(x1, x__1)]"));
  }

  @Test
  public void testPrintSubstitutionWithTwoRenamings() {
    TRS trs = exampleTrs();
    Printer printer = PrinterFactory.createUnicodePrinter(trs);
    
    Type itype = CoraInputReader.readType("Int");
    Variable x = TermFactory.createVar("x", itype);
    Variable y = TermFactory.createVar("x", itype);
    Variable z = TermFactory.createBinder("z", itype);
    MetaVariable zz = TermFactory.createMetaVar("Z", CoraInputReader.readType("Int -> Int"), 1);
    Term zz0 = TermFactory.createMeta(zz, TheoryFactory.createValue(0));
    Term faxy = trs.lookupSymbol("f").apply(trs.lookupSymbol("a").apply(x)).apply(y);
    Term lfzx = TermFactory.createAbstraction(z, trs.lookupSymbol("f").apply(z).apply(x));

    Renaming keys = printer.generateUniqueNaming(x, zz0);
    Renaming values = printer.generateUniqueNaming(faxy, lfzx);

    Substitution gamma = TermFactory.createEmptySubstitution();
    PrintableObject o = printer.makePrintable(gamma, keys, values);

    // []
    printer.add(o);
    assertTrue(printer.toString().equals("[]"));

    // [x := f(a(x),y)]
    printer = PrinterFactory.createUnicodePrinter(trs);
    gamma.extend(x, faxy);
    printer.add(o, "\n");

    // [x := f(a(x), y); Z := λz.f(z,x)]
    gamma.extend(zz, lfzx);
    printer.add(o);

    assertTrue(printer.toString().equals("[x := f(a(x__1), x__2)]\n" +
      "[x := f(a(x__1), x__2), Z := λz.f(z, x__1)]"));
  }

  @Test
  public void testMissingKeyInSubstitutionPrint() {
    Substitution gamma = TermFactory.createEmptySubstitution();
    TRS trs = exampleTrs();
    Term fx3 = CoraInputReader.readTerm("f(x, 3)", trs);
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(TermFactory.createVar("x", CoraInputReader.readType("Int")), fx3);
    Printer printer = PrinterFactory.createUnicodePrinter(trs);
    Renaming renaming = printer.generateUniqueNaming(fx3);
    assertThrows(IllegalArgumentException.class, () ->
      printer.add(new Pair<Substitution,Renaming>(subst, renaming)));
  }

  @Test
  public void testUnsupportedAdd() {
    Printer printer = PrinterFactory.createUnicodePrinter(exampleTrs());
    assertThrows(Printer.PrintingUnknownObjectException.class, () ->
      printer.add("hello", exampleTrs()));
    assertThrows(Printer.PrintingUnknownObjectException.class, () ->
      printer.add("this is optional", java.util.Optional.of(TermFactory.createVar("x")), "see?"));
    assertThrows(Printer.PrintingUnknownObjectException.class, () ->
      printer.add(List.of("x", TermFactory.createEmptySubstitution())));
    assertThrows(Printer.PrintingUnknownObjectException.class, () ->
      printer.add(new Pair<String,String>("a", "b")));
  }
}
