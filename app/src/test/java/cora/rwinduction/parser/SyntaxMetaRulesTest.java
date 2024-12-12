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

package cora.rwinduction.parser;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.util.Either;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.Command;
import cora.rwinduction.interactive.CmdMetaRules;

class SyntaxMetaRulesTest {
  TRS trs = CoraInputReader.readTrsFromString (
    "sum :: Int -> Int\n" +
    "sum(x) -> 0         | x ≤ 0\n" +
    "sum(x) -> x + sum(x - 1) | x > 0"
  );

  @Test
  public void testBasics() {
    Syntax syntax = new SyntaxMetaRules(trs);
    assertTrue(syntax.queryName().equals(":rules"));
    assertTrue(syntax.callDescriptor().get(0).equals(":rules"));
    assertTrue(syntax.callDescriptor().get(1).equals(":rules <function symbol>"));
  }

  @Test
  public void testParseStandalone() {
    Syntax syntax = new SyntaxMetaRules(trs);
    Either<String,Command> e = syntax.parse("");
    Command cmd = switch (e) {
      case Either.Left(String str) -> {
        assertTrue(false, "Standalone command yields string: " + str);
        yield null;
      }
      case Either.Right(Command c) -> c;
    };
    assertTrue(((CmdMetaRules)cmd).queryStartSymbol() == null);
  }

  @Test
  public void testParseSymbol() {
    Syntax syntax = new SyntaxMetaRules(trs);
    Either<String,Command> e = syntax.parse("sum");
    Command cmd = switch (e) {
      case Either.Left(String str) -> {
        assertTrue(false, "Standalone command yields string: " + str);
        yield null;
      }
      case Either.Right(Command c) -> c;
    };
    assertTrue(((CmdMetaRules)cmd).queryStartSymbol().equals(trs.lookupSymbol("sum")));
  }

  @Test
  public void testParseCalculationSymbol() {
    Syntax syntax = new SyntaxMetaRules(trs);
    Either<String,Command> e = syntax.parse("[=_Bool]");
    Command cmd = switch (e) {
      case Either.Left(String str) -> {
        assertTrue(false, "Standalone command yields string: " + str);
        yield null;
      }
      case Either.Right(Command c) -> c;
    };
    assertTrue(((CmdMetaRules)cmd).queryStartSymbol().toString().equals("[⇔]"));
    assertTrue(((CmdMetaRules)cmd).queryStartSymbol().queryType().toString().equals(
      "Bool → Bool → Bool"));
  }

  @Test
  public void testParseTwoArguments() {
    Syntax syntax = new SyntaxMetaRules(trs);
    Either<String,Command> e = syntax.parse("sum +");
    switch (e) {
      case Either.Left(String str):
        assertTrue(str.equals("Too many arguments: :rules takes 0 or 1"));
        break;
      case Either.Right(Command c): assertTrue(false, "I could parse sum +!");
    }
  }

  @Test
  public void testParseUnknownArgument() {
    Syntax syntax = new SyntaxMetaRules(trs);
    Either<String,Command> e = syntax.parse("sum2");
    switch (e) {
      case Either.Left(String str):
        assertTrue(str.equals("1:1: Undeclared symbol: sum2.  " +
          "Type cannot easily be deduced from context."));
        break;
      case Either.Right(Command c): assertTrue(false, "I could parse sum2!");
    }
  }

  @Test
  public void testParseUnknownCalculation() {
    Syntax syntax = new SyntaxMetaRules(trs);
    Either<String,Command> e = syntax.parse("[and]");
    switch (e) {
      case Either.Left(String str):
        assertTrue(str.equals("1:2: Expected infix symbol but got IDENTIFIER (and)"));
        break;
      case Either.Right(Command c): assertTrue(false, "I could parse sum2!");
    }
  }
}

