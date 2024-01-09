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
import cora.types.Type;
import cora.parser.lib.ErrorCollector;
import cora.parser.CoraParser;
import cora.types.TypeFactory;
import cora.terms.*;

public class CoraInputReaderTest {
  private Type type(String str) {
    return CoraParser.readType(str);
  }

  private SymbolData makeBasicData() {
    SymbolData data = new SymbolData();
    data.addFunctionSymbol(TermFactory.createConstant("f", type("a → b")));
    data.addFunctionSymbol(TermFactory.createConstant("aa", type("a")));
    data.addFunctionSymbol(TermFactory.createConstant("bb", type("b")));
    data.addFunctionSymbol(TermFactory.createConstant("h", type("a → b → b")));
    data.addFunctionSymbol(TermFactory.createConstant("i", type("b → a")));
    data.addFunctionSymbol(TermFactory.createConstant("map", type("(nat → nat) → list → list")));
    data.addFunctionSymbol(TermFactory.createConstant("cons", type("nat → list → list")));
    return data;
  }

  @Test
  public void testCorrectDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    SymbolData data = makeBasicData();
    String str = "g :: a -> (b -> c) -> d\ng(x,y) -> h";
    CoraInputReader.readDeclarationForUnitTest(str, data, false, collector);
    assertTrue(data.lookupFunctionSymbol("g").queryType().toString().equals("a ⇒ (b ⇒ c) ⇒ d"));
    System.out.println(collector.queryCollectedMessages());
  }

  @Test
  public void testDeclarationWithPreviouslyDeclaredName() {
    ErrorCollector collector = new ErrorCollector(10);
    SymbolData data = makeBasicData();
    String str = "f :: a -> (b -> c)";
    CoraInputReader.readDeclarationForUnitTest(str, data, true, collector);
    assertTrue(data.lookupFunctionSymbol("f").queryType().toString().equals("a ⇒ b"));
    assertTrue(collector.queryCollectedMessages().equals(
      "1:1: Redeclaration of previously declared function symbol f.\n"));
  }

  // no tests yet for public and private, because we don't yet support this in cora.rewriting
}

