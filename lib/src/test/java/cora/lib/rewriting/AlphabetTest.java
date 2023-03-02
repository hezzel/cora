/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.lib.rewriting;

import org.junit.Test;
import static org.junit.Assert.*;
import java.lang.Error;
import java.util.ArrayList;
import cora.lib.exceptions.NullInitialisationError;
import cora.lib.exceptions.TypingError;
import cora.lib.types.*;
import cora.lib.terms.FunctionSymbol;
import cora.lib.terms.TermFactory;

public class AlphabetTest {
  private Type baseType(String name) {
    return TypeFactory.createSort(name);
  }

  private FunctionSymbol makeConstant(String name, String sort) {
    return TermFactory.createConstant(name, baseType(sort));
  }

  private FunctionSymbol makeSymbol(String name, Type type) {
    return TermFactory.createConstant(name, type);
  }

  @Test
  public void testBasics() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(makeConstant("0", "Nat"));
    symbols.add(makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("Nat"))));
    Alphabet a = new Alphabet(symbols);
    assertTrue(a.lookup("0").equals(symbols.get(0)));
    assertTrue(a.lookup("S").equals(symbols.get(1)));
    assertTrue(a.lookup("s") == null);  // it's case-sensitive!
  }

  @Test
  public void testDuplicateAcceptable() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(makeConstant("0", "Nat"));
    symbols.add(makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("Nat"))));
    symbols.add(makeConstant("0", "Nat"));
    symbols.add(makeConstant("0", "Nat"));
    Alphabet a = new Alphabet(symbols);
    assertTrue(a.lookup("0").equals(symbols.get(0)));
    assertTrue(a.lookup("S").equals(symbols.get(1)));
  }

  @Test(expected = NullInitialisationError.class)
  public void testAlphabetNullInitialisation() {
    Alphabet a = new Alphabet(null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testAlphabetNullSymbolInitialisation() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(makeConstant("0", "Nat"));
    symbols.add(null);
    symbols.add(makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("Nat"))));
    Alphabet a = new Alphabet(symbols);
  }

  @Test(expected = TypingError.class)
  public void testUnacceptableDuplicate() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(makeConstant("0", "Nat"));
    symbols.add(makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("Nat"))));
    symbols.add(makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("nat"))));
      // Nat vs nat
    Alphabet a = new Alphabet(symbols);
  }
}
