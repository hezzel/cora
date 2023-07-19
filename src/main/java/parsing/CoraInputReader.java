/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsing;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Set;
import java.util.TreeMap;
import cora.exceptions.IllegalRuleError;
import cora.exceptions.ParseError;
import cora.parsing.lib.Token;
import cora.parsing.lib.ParsingStatus;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.*;

/** This class reads text from string or file written in the internal .cora format. */
public class CoraInputReader {
  /**
   * The reader keeps track of the status of reading so far; all read functions have a (potential)
   * side effect of advancing the parsing status.
   */
  private ParsingStatus _status;
  /**
   * The reader keeps track of the declared variables, and the function symbols encountered so far.
   */
  private SymbolData _symbols;

  /**
   * Stores the parsing status for use by methods of the CoraInputReader class.
   * Private because it should only be called by the static methods that use a CoraInputReader.
   */
  private CoraInputReader(ParsingStatus status) {
    _status = status;
    _symbols = new SymbolData();
  }

  /**
   * Stores the parsing status for use by methods of the CoraInputReader class, and stores the
   * given TRS into the SymbolData used to parse terms.
   * Private because it should only be called by the static methods that use a CoraInputReader.
   */
  private CoraInputReader(ParsingStatus status, TRS trs) {
    _status = status;
    _symbols = new SymbolData(trs);
  }

  // ===================================== PARSING CONSTANTS ======================================

  /**
   * string := STRING+
   *
   * This function checks if the next tokens represent a string, and if so, read them and return
   * this string.  If not, null is returned and nothing is read.
   */
  private String tryReadString() {
    Token next;
    StringBuilder ret = null;
    while ((next = _status.readNextIf(CoraTokenData.STRING)) != null) {
      if (ret == null) ret = new StringBuilder(next.getText());
      else ret.append(next.getText());
    }
    if (ret == null) return null;
    return ret.toString();
  }

  /**
   * constant ::= IDENTIFIER | string
   *
   * This function checks if the next tokens represent a constant, and if so, read them and return
   * this constant.  If not, null is returned and nothing is read.
   */
  private String tryReadConstant() {
    Token next = _status.readNextIf(CoraTokenData.IDENTIFIER);
    if (next != null) return next.getText();
    return tryReadString();
  }

  // ======================================== PARSING TYPES =======================================

  /**
   * typearrow := TYPEARROW | ARROW
   *
   * This function checks if the next token is one of the two arrows that may be used for types,
   * and if so, reads it and returns true.  If not, false is returned instead.
   *
   * If a RULEARROW is given instead, then it will also be read (since a rule arrow should never
   * occur at the place of a type arrow), but an error is stored.
   */
  private boolean tryReadTypeArrow() {
    if (_status.readNextIf(CoraTokenData.TYPEARROW) != null) return true;
    if (_status.readNextIf(CoraTokenData.ARROW) != null) return true;
    // error handling
    Token token = _status.readNextIf(CoraTokenData.RULEARROW);
    if (token != null) {
      _status.storeError("Rule arrow → occurs in a type; did you mean ⇒?", token);
      return true;
    }
    return false;
  }

  /**
   * type ::= constant (typearrow type)?
   *        | BRACKETOPEN type BRACKETCLOSE (typearrow type)?
   *
   * This function reads a type and returns it.
   * The input is expected to actually be a type. If this is not the case, then an error is stored.
   * If some kind of error recovery could be done, a Type is still returned; otherwise, null may be
   * returned, even if something was read -- indicating that we will have to do large-scale error
   * recovery.
   */
  private Type readType() {
    Type start;

    String constant = tryReadConstant();
    if (constant == null) {
      Token bracket = _status.expect(CoraTokenData.BRACKETOPEN,
        "a type (started by a constant or bracket)");
      if (bracket == null) { // error recovery
        if (tryReadTypeArrow()) return readType();  // maybe we have -> type or () -> type
        return null;                                // otherwise, no idea what they're trying to do
      }
      start = readType();
      if (_status.expect(CoraTokenData.BRACKETCLOSE, "closing bracket") == null) return start;
    }
    else start = TypeFactory.createSort(constant);

    if (!tryReadTypeArrow()) return start;
    
    Type end = readType();
    if (start == null) return end;
    if (end == null) return start;
    return TypeFactory.createArrow(start, end);
  }

  // ========================= READING FUNCTION AND VARIABLE DECLARATIONS =========================


  // ============================= HELPER FUNCTIONALITY FOR UNIT TESTS ============================

  static Type readTypeForUnitTest(ParsingStatus ps) {
    CoraInputReader reader = new CoraInputReader(ps);
    return reader.readType();
  }

  // ================================= FUNCTIONS FOR INTERNAL USE =================================

  /** Reads the given type from string */
  public static Type readTypeFromString(String str) {
    ParsingStatus status = new ParsingStatus(CoraTokenData.getStringLexer(str), 10);
    CoraInputReader reader = new CoraInputReader(status);
    Type ret = reader.readType();
    Token token = status.nextToken();
    if (!token.isEof()) status.storeError("String continues after type has ended.", token);
    status.throwCollectedErrors();
    return ret;
  }
}

