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

package charlie.trs;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.List;

import charlie.exceptions.NullStorageException;
import charlie.exceptions.TypingException;
import charlie.util.LookupMap;
import charlie.types.*;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;

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
  public void testAdd() {
    FunctionSymbol zero = makeConstant("0", "Nat");
    FunctionSymbol s = makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("Nat")));
    Alphabet alf1 = new Alphabet(List.of(zero, s));
    FunctionSymbol a = makeConstant("a", "A");
    FunctionSymbol b = makeConstant("b", "A");
    FunctionSymbol c = makeConstant("a", "C");
    FunctionSymbol d = makeConstant("0", "C");
    Alphabet alf2 = alf1.add(List.of(a, s, b));
    assertTrue(alf1.lookup("0") == zero);
    assertTrue(alf1.lookup("S") == s);
    assertTrue(alf1.lookup("a") == null);
    assertTrue(alf1.lookup("b") == null);
    assertTrue(alf2.lookup("0") == zero);
    assertTrue(alf2.lookup("S") == s);
    assertTrue(alf2.lookup("a") == a);
    assertTrue(alf2.lookup("b") == b);
    alf1.add(List.of(b, c));  // no problem here
    assertThrows(TypingException.class, () -> alf2.add(List.of(b, c)));
    assertThrows(TypingException.class, () -> alf1.add(List.of(d)));
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

  @Test
  public void testAlphabetNullInitialisation() {
    LookupMap<FunctionSymbol> map1 = null;
    ArrayList<FunctionSymbol> map2 = null;
    assertThrows(NullStorageException.class, () -> new Alphabet(map1));
    assertThrows(NullStorageException.class, () -> new Alphabet(map2));
  }

  @Test
  public void testAlphabetNullSymbolInitialisation() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(makeConstant("0", "Nat"));
    symbols.add(null);
    symbols.add(makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("Nat"))));
    assertThrows(NullStorageException.class, () ->new Alphabet(symbols));
  }

  @Test
  public void testUnacceptableDuplicate() {
    ArrayList<FunctionSymbol> symbols = new ArrayList<FunctionSymbol>();
    symbols.add(makeConstant("0", "Nat"));
    symbols.add(makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("Nat"))));
    symbols.add(makeSymbol("S", TypeFactory.createArrow(baseType("Nat"), baseType("nat"))));
      // Nat vs nat
    assertThrows(TypingException.class, () -> new Alphabet(symbols));
  }
}
