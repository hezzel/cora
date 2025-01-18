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

import charlie.terms.*;
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
  public void testUnicode() {
    CommandParsingStatus status = new CommandParsingStatus("ak:jfda 11 #1341∀Ê ; aa");
    assertTrue(status.nextWord().equals("ak:jfda"));
    assertTrue(status.nextWord().equals("11"));
    assertTrue(status.nextWord().equals("#1341∀Ê"));
    assertTrue(status.skipSeparator());
    assertTrue(status.nextWord().equals("aa"));
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
  // reading substitutions

  @Test
  public void testParseSubstitution() {
    Variable x = TermFactory.createVar(CoraInputReader.readType("Int"));
    Variable z = TermFactory.createVar(CoraInputReader.readType("Int"));
    Renaming keys = new Renaming(trs.queryFunctionSymbolNames());
    keys.setName(x, "x");
    keys.setName(z, "z");
    Renaming values = new Renaming(trs.queryFunctionSymbolNames());
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
    Renaming keys = new Renaming(trs.queryFunctionSymbolNames());
    Renaming values = new Renaming(trs.queryFunctionSymbolNames());
    Substitution subst = status.readSubstitution(trs, keys, values, module);
    assertTrue(subst != null);
    assertTrue(status.commandEnded());
  }

  @Test
  public void testMissingKeyInSubstitution() {
    Renaming keys = new Renaming(trs.queryFunctionSymbolNames());
    keys.setName(TermFactory.createVar("z", CoraInputReader.readType("Int")), "z");
    Renaming values = new Renaming(trs.queryFunctionSymbolNames());
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
    Renaming keys = new Renaming(trs.queryFunctionSymbolNames());
    keys.setName(x, "x");
    keys.setName(z, "z");
    Renaming values = new Renaming(trs.queryFunctionSymbolNames());
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
    Renaming keys = new Renaming(trs.queryFunctionSymbolNames());
    keys.setName(x, "x");
    keys.setName(z, "z");
    Renaming values = new Renaming(trs.queryFunctionSymbolNames());
    CommandParsingStatus status = new CommandParsingStatus("[x := x + sum(y), z := sum(3)]");
    OutputModule module = OutputModule.createUnicodeModule(trs);
    assertTrue(status.readSubstitution(trs, keys, values, module) == null);
    assertTrue(status.commandEnded());
    assertTrue(module.toString().equals("Ill-typed substitution: z has type Bool but is mapped " +
      "to a term sum(3) of type Int.\n\n"));
  }
}
