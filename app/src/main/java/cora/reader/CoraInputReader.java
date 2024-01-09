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

package cora.reader;

import java.io.IOException;
import java.util.ArrayList;

import com.google.common.collect.ImmutableList;
import cora.exceptions.*;
import cora.utils.LookupMap;
import cora.parser.lib.Token;
import cora.parser.lib.ErrorCollector;
import cora.parser.Parser.*;
import cora.parser.CoraParser;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.*;

/**
 * This class reads text from string or file written in Cora's internal formalism(s).  Specific
 * restrictions are imposed depending on the exact type (e.g., constrained / unconstrained, and
 * applicative or with lambda / meta-variables).
 */
public class CoraInputReader extends TermTyper {
  /**
   * Stores the parsing status for use by methods of the CoraInputReader class.
   * Private because it should only be called by the static methods that use a CoraInputReader.
   */
  private CoraInputReader(SymbolData data, ErrorCollector collector) {
    super(data, collector);
  }

  // ==================================== READING DECLARATIONS ====================================

  /** takes a parser declaration and stores it as a function symbol declaration */
  private void handleFunctionDeclaration(ParserDeclaration decl) {
    if (decl == null || decl.type() == null) return;
    String name = decl.name();
    if (_symbols.lookupFunctionSymbol(name) != null) {
      storeError("Redeclaration of previously declared function symbol " + name + ".",
                 decl.token());
    }
    else _symbols.addFunctionSymbol(TermFactory.createConstant(name, decl.type()));
  }

  /** takes a set of parser declarations and stores them as variable declarations */
  private void readEnvironment(LookupMap<ParserDeclaration> vars) {
    // TODO
  }

  // ======================================= READING FULL TRSS ====================================

  /**
   * Either returns a valid rule, or returns null and potentially stores an erorr if the given
   * parser rule does not define a valid rule.
   */
  private Rule makeRule(ParserRule rule) {
    _symbols.clearEnvironment();
    readEnvironment(rule.vars());
    Term l = null, r = null, c = null;
    if (!rule.left().hasErrors()) l = makeTerm(rule.left(), null, true);
    if (!rule.right().hasErrors()) {
      Type expected = null;
      if (l != null) expected = l.queryType();
      r = makeTerm(rule.right(), expected, false);
    }
    if (rule.constraint() != null && !rule.constraint().hasErrors()) {
      c = makeTerm(rule.constraint(), TypeFactory.boolSort, true);
    }
    if (l == null || r == null) return null;
    
    try {
      if (c == null) return RuleFactory.createRule(l, r);
      else return RuleFactory.createRule(l, r, c);
    }
    catch (IllegalRuleError e) {
      storeError(e.queryProblem(), rule.token());
      return null;
    }
  }

  // =============================== ACCESS FUNCTIONS FOR UNIT TESTS ==============================

  /** Symbol declaration */
  static void readDeclarationForUnitTest(String str, SymbolData data, boolean constrained,
                                         ErrorCollector collector) {
    ParserDeclaration decl = CoraParser.readDeclaration(str, constrained, collector);
    CoraInputReader reader = new CoraInputReader(data, collector);
    reader.handleFunctionDeclaration(decl);
  }

  // ==================================== PUBLIC FUNCTIONALITY ====================================

  /**
   * Reads the given type from string.
   * If constrainedTRS is set to true, then Int, Bool and String are recognised as pre-defined
   * sorts, and identifiers are restricted as they are when reading a constrained TRS (e.g., sort
   * names may not contain "+").  If it is set to false, then identifiers are more general and
   * the pre-defined types will not be marked as theory sorts.
   */
  public static Type readType(String str, boolean constrainedTRS) {
    return CoraParser.readType(str, constrainedTRS, null);
  }

  /**
   * Reads the given type from string, recognising the pre-defined sorts.
   * This is the same as readTypeFromString(true).
   */
  public static Type readType(String str) {
    return CoraParser.readType(str);
  }

  /**
   * Reads the given term from string.
   * The TRS is used for its alphabet (function symbols are automatically recognised), and to
   * know whether or not we should include theories.  The rules and rule schemes are ignored.
   */
  public static Term readTerm(String str, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    ParserTerm pt = CoraParser.readTerm(str, trs.isConstrained(), collector);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    SymbolData data = new SymbolData(trs);
    CoraInputReader reader = new CoraInputReader(data, collector);
    Term ret = reader.makeTerm(pt, null, true);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  }

  /**
   * Reads the given term from string.
   * The TRS is used for its alphabet (function symbols are automatically recognised), and to
   * know whether or not we should include theories.  The rules and rule schemes are ignored.
   */
  public static Rule readRule(String str, TRS trs) {
    ErrorCollector collector = new ErrorCollector();
    ParserRule rule = CoraParser.readRule(str, trs.isConstrained(), collector);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    SymbolData data = new SymbolData(trs);
    CoraInputReader reader = new CoraInputReader(data, collector);
    Rule ret = reader.makeRule(rule);
    if (collector.queryErrorCount() > 0) throw new ParseError(collector.queryCollectedMessages());
    return ret;
  } 
}
