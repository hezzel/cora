/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.parser;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Optional;

import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.substitution.Substitution;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;

class CommandParsingStatusTest {
  // ==============================================================================================
  // basic usage
  
  @Test
  public void testReadingWords() {
    CommandParsingStatus status = new CommandParsingStatus("Hello world! This is me.");
    assertTrue(status.nextWord().equals("Hello"));
    assertTrue(status.nextWord().equals("world!"));
    assertTrue(status.nextWord().equals("This"));
    assertFalse(status.done());
    assertFalse(status.commandEnded());
    assertFalse(status.skipSeparator());
    assertTrue(status.previousPosition() == 14);
    assertTrue(status.nextWord().equals("is"));
    assertTrue(status.nextWord().equals("me."));
    assertTrue(status.done());
    assertTrue(status.commandEnded());
    assertTrue(status.nextWord() == null);
    assertTrue(status.commandEnded());
    assertFalse(status.skipSeparator());
  }

  @Test
  public void testWhitespace() {
    // include spaces, tabs and newlines, and have whitespace at beginning and end
    CommandParsingStatus status = new CommandParsingStatus("  dfa aj;bfaa	 \n  test  \n\n");
    assertTrue(status.nextWord().equals("dfa"));
    assertTrue(status.previousPosition() == 3);
    assertTrue(status.nextWord().equals("aj"));
    assertTrue(status.skipSeparator());
    assertTrue(status.nextWord().equals("bfaa"));
    assertTrue(status.nextWord().equals("test"));
    assertTrue(status.nextWord() == null);
  }

  @Test
  public void testSemiColons() {
    CommandParsingStatus status = new CommandParsingStatus("ab;c d ;  e ; ;  g$ ;; h;;d");
    assertFalse(status.commandEnded());
    assertTrue(status.nextWord().equals("ab"));
    assertTrue(status.commandEnded());
    assertFalse(status.done());
    assertTrue(status.skipSeparator());
    assertTrue(status.nextWord().equals("c"));
    assertTrue(status.nextWord().equals("d"));
    assertTrue(status.nextWord() == null);
    assertTrue(status.skipSeparator());
    assertTrue(status.nextWord().equals("e"));
    assertTrue(status.commandEnded());
    assertTrue(status.skipSeparator());
    assertTrue(status.commandEnded());
    assertTrue(status.skipSeparator());
    assertFalse(status.skipSeparator());
    assertTrue(status.nextWord().equals("g$"));
    assertTrue(status.skipSeparator());
    assertTrue(status.skipSeparator());
    assertTrue(status.nextWord().equals("h"));
    assertTrue(status.skipSeparator());
    assertTrue(status.skipSeparator());
    assertTrue(status.nextWord().equals("d"));
    assertFalse(status.skipSeparator());
    assertTrue(status.done());
  }

  @Test
  public void testReadRest() {
    CommandParsingStatus status = new CommandParsingStatus("hello there sweet world; a e ;next ");
    assertTrue(status.nextWord().equals("hello"));
    assertTrue(status.readRest().equals("there sweet world"));
    assertTrue(status.skipSeparator());
    assertTrue(status.readRest().equals("a e "));
    assertTrue(status.skipSeparator());
    assertTrue(status.readRest().equals("next "));
    assertTrue(status.done());
  }

  @Test
  public void testUnicode() {
    CommandParsingStatus status = new CommandParsingStatus("ak:jfda 11 #1341∀Ê ; aa");
    assertTrue(status.nextWord().equals("ak:jfda"));
    assertTrue(status.nextWord().equals("11"));
    assertTrue(status.nextWord().equals("#1341∀Ê"));
    assertTrue(status.skipSeparator());
    assertTrue(status.nextWord().equals("aa"));
  }

  @Test
  public void testExpect() {
    CommandParsingStatus status = new CommandParsingStatus("ak:jfda   11 #1341∀Ê ; aa");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> om = Optional.of(module);
    assertTrue(status.expect("ak:", om));
    assertTrue(status.expect("jfda ", om));
    assertTrue(status.expect("11", om));
    assertFalse(status.expect("#1341AE", om));
    assertTrue(status.expect(";", om));
    assertTrue(status.expect("a", om));
    assertTrue(status.expect("a", om));
    assertTrue(module.toString().equals(
      "Unexpected input at position 14; I expected #1341AE but got #1341∀Ê.\n\n"));
  }

  // ==============================================================================================
  // reading function symbols

  TRS trs = CoraInputReader.readTrsFromString (
    "sum :: Int -> Int\n" +
    "sum(x) -> 0         | x ≤ 0\n" +
    "sum(x) -> x + sum(x - 1) | x > 0"
  );

  @Test
  public void testReadSymbol() {
    CommandParsingStatus status = new CommandParsingStatus("a sum - b");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(status.readSymbol(trs, module) == null);
    assertTrue(status.readSymbol(trs, module).toString().equals("sum"));
    assertTrue(status.readSymbol(trs, module).toString().equals("[-]"));
    assertTrue(status.readSymbol(trs, module) == null);
    assertTrue(status.readSymbol(trs, module) == null);
    assertTrue(module.toString().equals(
      "Parsing error at position 1: Undeclared symbol: a.  Type cannot easily be deduced from context.\n\n" +
      "Parsing error at position 9: Undeclared symbol: b.  Type cannot easily be deduced from context.\n\n" +
      "Parsing error at position 10: Expected function symbol (or variable) name but got end of input.\n\n"));
  }

  // ==============================================================================================
  // reading identifiers

  @Test
  public void testReadIdentifier() {
    CommandParsingStatus status = new CommandParsingStatus("xx   aaa b sum 12 test - m:eh");
    OutputModule o = OutputModule.createUnicodeModule(trs);
    Optional<OutputModule> module = Optional.of(o);
    assertTrue(status.readIdentifier(module, "test1").equals("xx"));
    assertTrue(status.readIdentifier(module, "test2").equals("aaa"));
    assertTrue(status.readIdentifier(module, "test3").equals("b"));
    assertTrue(status.readIdentifier(module, "test4").equals("sum"));
    assertTrue(status.readIdentifier(module, "test5") == null);
    status.nextWord();
    assertTrue(status.readIdentifier(module, "test6").equals("test"));
    assertTrue(status.readIdentifier(module, "test7") == null);
    status.nextWord();
    assertTrue(status.readIdentifier(module, "test8").equals("m"));
    assertTrue(status.readIdentifier(module, "test9") == null);
    assertTrue(status.readIdentifier(module, "test10") == null);
    assertTrue(o.toString().equals(
      "Parsing error at position 16: Expected test5 but got INTEGER (12).\n\n" +
      "Parsing error at position 24: Expected test7 but got MINUS (-).\n\n" +
      "Parsing error at position 27: Expected test9 but got COLON (:).\n\n" +
      "Parsing error at position 27: Expected test10 but got COLON (:).\n\n"));
  }

  // ==============================================================================================
  // reading terms

  @Test
  public void testReadTerm() {
    CommandParsingStatus status = new CommandParsingStatus("test x+  sum(3) y");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    status.nextWord();
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    Term t = status.readTerm(trs, renaming, module);
    assertTrue(module.toString().equals(""));
    assertTrue(t.toString().equals("x + sum(3)"));
    assertTrue(renaming.domain().size() == 0);
    assertTrue(status.previousPosition() == 6);
    assertTrue(status.nextWord().equals("y"));
  }

  @Test
  public void testReadVariable() {
    CommandParsingStatus status = new CommandParsingStatus("myvar");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    renaming.setName(TermFactory.createVar(CoraInputReader.readType("A")), "myvar");
    Term t = status.readTerm(trs, renaming, module);
    assertTrue(module.toString().equals(""));
    assertTrue(t.isVariable());
    assertTrue(t.queryType().toString().equals("A"));
    assertTrue(renaming.getReplaceable("myvar") == t);
  }

  @Test
  public void testReadFreshVariable() {
    CommandParsingStatus status = new CommandParsingStatus("  myvar");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    MutableRenaming renaming = new MutableRenaming(trs.queryFunctionSymbolNames());
    assertTrue(status.readTerm(trs, renaming, module) == null);
    assertTrue(module.toString().equals("Unknown variable: myvar\n\n"));
  }

  // ==============================================================================================
  // reading substitutions

  @Test
  public void testParseSubstitution() {
    Variable x = TermFactory.createVar(CoraInputReader.readType("Int"));
    Variable z = TermFactory.createVar(CoraInputReader.readType("Int"));
    MutableRenaming keys = new MutableRenaming(trs.queryFunctionSymbolNames());
    keys.setName(x, "x");
    keys.setName(z, "z");
    MutableRenaming values = new MutableRenaming(trs.queryFunctionSymbolNames());
    Term t1 = CoraInputReader.readTermAndUpdateNaming("x + sum(y)", values, trs);
    Term t2 = CoraInputReader.readTermAndUpdateNaming("sum(3)", values, trs);
    CommandParsingStatus status = new CommandParsingStatus(" X [x := x + sum(y), z := sum(3)] Y");
    status.nextWord();  // skip past "X"
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Substitution subst = status.readSubstitution(trs, keys, values, module);
    assertTrue(subst != null);
    assertTrue(subst.get(x).equals(t1));
    assertTrue(subst.get(z).equals(t2));
    assertTrue(status.nextWord().equals("Y"));
  }

  @Test
  public void testParseEmptySubstitution() {
    CommandParsingStatus status = new CommandParsingStatus(" [] ");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    MutableRenaming keys = new MutableRenaming(trs.queryFunctionSymbolNames());
    MutableRenaming values = new MutableRenaming(trs.queryFunctionSymbolNames());
    Substitution subst = status.readSubstitution(trs, keys, values, module);
    assertTrue(subst != null);
    assertTrue(status.commandEnded());
  }

  @Test
  public void testMissingKeyInSubstitution() {
    MutableRenaming keys = new MutableRenaming(trs.queryFunctionSymbolNames());
    keys.setName(TermFactory.createVar("z", CoraInputReader.readType("Int")), "z");
    MutableRenaming values = new MutableRenaming(trs.queryFunctionSymbolNames());
    Term t1 = CoraInputReader.readTermAndUpdateNaming("x + sum(y)", values, trs);
    CommandParsingStatus status = new CommandParsingStatus("[x := x + sum(y), z := sum(3)] Z");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(status.readSubstitution(trs, keys, values, module) == null);
    assertTrue(status.nextWord().equals("Z"));
    assertTrue(module.toString().equals("Parsing error at position 2: No such variable: x\n\n"));
  }

  @Test
  public void testSubstitutionMissingVariableInValue() {
    Variable x = TermFactory.createVar(CoraInputReader.readType("Int"));
    Variable z = TermFactory.createVar(CoraInputReader.readType("Int"));
    MutableRenaming keys = new MutableRenaming(trs.queryFunctionSymbolNames());
    keys.setName(x, "x");
    keys.setName(z, "z");
    MutableRenaming values = new MutableRenaming(trs.queryFunctionSymbolNames());
    CommandParsingStatus status = new CommandParsingStatus("[x := x + sum(y), z := sum(3)]");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    Substitution subst = status.readSubstitution(trs, keys, values, module);
    assertTrue(subst.get(x).toString().equals("x + sum(y)"));
    assertTrue(subst.get(z).toString().equals("sum(3)"));
    assertTrue(values.getReplaceable("x") != null);
    assertTrue(values.getReplaceable("y") != null);
    assertTrue(values.getReplaceable("z") == null);
    assertTrue(module.toString().equals(""));
  }

  @Test
  public void testIllTypedSubstitution() {
    Variable x = TermFactory.createVar(CoraInputReader.readType("Int"));
    Variable z = TermFactory.createVar(CoraInputReader.readType("Bool"));
    MutableRenaming keys = new MutableRenaming(trs.queryFunctionSymbolNames());
    keys.setName(x, "x");
    keys.setName(z, "z");
    MutableRenaming values = new MutableRenaming(trs.queryFunctionSymbolNames());
    CommandParsingStatus status = new CommandParsingStatus("[x := x + sum(y), z := sum(3)]");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(status.readSubstitution(trs, keys, values, module) == null);
    assertTrue(status.commandEnded());
    assertTrue(module.toString().equals("Parsing error at position 24: Type error: expected " +
      "term of type Bool, but got sum(3) of type Int.\n\n"));
  }
}
