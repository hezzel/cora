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

package charlie.parser;

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.util.ArrayList;
import java.util.TreeSet;

import charlie.util.LookupMap;
import charlie.types.*;
import charlie.parser.lib.*;
import charlie.parser.InfixManager.OperatorData;
import charlie.parser.Parser.*;

/**
 * The AriParser parses several of the ARI input formats (of the international termination and
 * confluence competition).
 */
public class AriParser {
  private ParsingStatus _status;
  private TreeSet<String> _sorts;
  private enum TrsFormat { HigherOrder };

  /**
   * Stores the parsing status for use by methods of the AriParser class.
   * Private because the AriParser should only be created by the static methods in the class.
   */
  private AriParser(ParsingStatus status) {
    _status = status;
  }

  // ======================================== READING TYPES =======================================
  
  /**
   * Advances the parsing status until after the next closing bracket (or more than one if we also
   * encounter opening brackets) or until the end of the input.
   */
  private void readUntilCloseBracket() {
    int open = 1;
    while (open > 0) {
      Token next = _status.nextToken();
      if (next.getName().equals(AriTokenData.BRACKETCLOSE)) open--;
      else if (next.getName().equals(AriTokenData.BRACKETOPEN)) open++;
      else if (next.isEof()) return;
    }
  }

  /**
   * This reads a type from input and returns it.  If the current input does not represent a type,
   * then an error is stored.  Note that all base types must be in the _sorts set; if this is not
   * the case then an error will be stored, but parsing will continue.
   *
   * Grammar: type := IDENTIFIER | ( ARROW type+ IDENTIFIER )
   */
  private Type readType() {
    // case: IDENTIFIER
    Token base = _status.readNextIf(AriTokenData.IDENTIFIER);
    if (base != null) {
      String name = base.getText();
      if (!_sorts.contains(name)) _status.storeError(base, "Undeclared sort: " + name);;
      return TypeFactory.createSort(name);
    }
    // remaining case: ( ARROW type+ IDENTIFIER )
    Token open = _status.expect(AriTokenData.BRACKETOPEN, "sort name or opening bracket");
    if (open == null) return null;
    _status.expect(AriTokenData.ARROW, "-> (arrow)");
    ArrayList<Type> parts = new ArrayList<Type>();
    do {
      Type arg = readType();
      if (arg == null) { readUntilCloseBracket(); return null; }
      parts.add(arg);
    } while (_status.readNextIf(AriTokenData.BRACKETCLOSE) == null);
    if (parts.size() == 0) { _status.storeError(open, "Empty type"); return null; }
    Type ret = parts.get(parts.size() -1 );
    for (int i = parts.size()-2; i >= 0; i--) ret = TypeFactory.createArrow(parts.get(i), ret);
    return ret;
  }

  // ======================================== READING TERMS =======================================

  /** This expects a closing bracket, and if there is not one, reads until one is found. */
  private void reallyExpectClosingBracket() {
    if (_status.expect(AriTokenData.BRACKETCLOSE, "closing bracket") == null) {
      readUntilCloseBracket();
    }
  }

  /**
   * This reads a term from the current parsing status.  Only limited error recovery is done if the
   * term is poorly formatted.  It is possible that null is returned if there are errors in the
   * specificiation.
   *
   * Grammar: term ::= IDENTIFIER | ( IDENTIFIER term+ ) | (LAMBDA (var+) term)
   */
  private ParserTerm readTerm() {
    // case: IDENTIFIER
    Token id = _status.readNextIf(AriTokenData.IDENTIFIER);
    if (id != null) return new Identifier(id, id.getText());

    if (_status.expect(AriTokenData.BRACKETOPEN, "opening bracket") == null) return null;

    // case: ( IDENTIFIER term+ )
    Token main = _status.readNextIf(AriTokenData.IDENTIFIER);
    if (main != null) {
      ImmutableList.Builder<ParserTerm> builder = ImmutableList.<ParserTerm>builder();
      while (_status.readNextIf(AriTokenData.BRACKETCLOSE) == null) {
        ParserTerm arg = readTerm();
        if (arg == null) { readUntilCloseBracket(); break; }
        builder.add(arg);
      }
      ImmutableList<ParserTerm> args = builder.build();
      if (args.size() == 0) {
        _status.storeError(main, "Identifier without arguments should not be in brackets.");
      }
      ParserTerm head = new Identifier(main, main.getText());
      return new Application(main, head, args);
    }

    // case: ( LAMBDA vars term )
    Token lambda = _status.expect(AriTokenData.LAMBDA, "identifier or lambda");
    if (lambda == null) return null;
    ArrayList<ParserDeclaration> vars = readLambdaVariables();
    ParserTerm term = readTerm();
    reallyExpectClosingBracket();
    if (term == null) return null;
    if (vars.size() == 0) {
      _status.storeError(lambda, "Lambda should have at least one variable.");
      return term;
    }
    for (int i = vars.size()-1; i >= 0; i--) {
      term = new Lambda(vars.get(i).token(), vars.get(i).name(), vars.get(i).type(), term);
    }
    return term;
  }

  /** Grammar: ( ( IDENTIFIER type )+ ) */
  private ArrayList<ParserDeclaration> readLambdaVariables() {
    ArrayList<ParserDeclaration> ret = new ArrayList<ParserDeclaration>();
    if (_status.expect(AriTokenData.BRACKETOPEN, "opening bracket (for variable declarations)")
      == null) return ret;
    while (_status.readNextIf(AriTokenData.BRACKETCLOSE) == null) {
      Token open = _status.expect(AriTokenData.BRACKETOPEN, "opening bracket");
      Token id = _status.expect(AriTokenData.IDENTIFIER, "identifier (variable name)");
      Type type = readType();
      if (open != null) reallyExpectClosingBracket();
      if (id == null && type == null) { reallyExpectClosingBracket(); return ret; }
      if (id != null && type != null) ret.add(new ParserDeclaration(open, id.getText(), type));
    }
    return ret;
  }

  // ==================================== READING FULL PROGRAMS ===================================

  /**
   * This reads the format token and returns it if it's one of the supported formats, or stores an
   * error and returns null if it is not one of the supported formats.
   *
   * Grammar: ( FORMAT IDENTIFIER )
   */
  private TrsFormat readFormat() {
    _status.expect(AriTokenData.BRACKETOPEN, "opening bracket");
    _status.expect(AriTokenData.FORMAT, "\"format\"");
    Token tmp = _status.expect(AriTokenData.IDENTIFIER, "identifier describing the format");
    _status.expect(AriTokenData.BRACKETCLOSE, "closing bracket");
    if (tmp == null) return null; // an error has already been stored
    if (tmp.getText().equals("higher-order")) return TrsFormat.HigherOrder;
    _status.storeError(tmp, "Format is not currently supported: " + tmp.getText());
    return null;
  }

  /**
   * This reads 0 or more sort declarations, and stores each sort into _sorts.
   *
   * Grammar: ( SORT IDENTIFIER )*
   */
  private void readSorts() {
    while (true) {
      Token open = _status.readNextIf(AriTokenData.BRACKETOPEN);
      if (open == null) return;
      if (_status.readNextIf(AriTokenData.SORT) == null) {
        _status.pushBack(open);
        return;
      }
      // we have read: ( SORT.  Now the next thing *has* to be an identifier indicating the
      // sort name
      Token name = _status.expect(AriTokenData.IDENTIFIER, "identifier (sort name)");
      _status.expect(AriTokenData.BRACKETCLOSE, "closing bracket");
      if (name != null) _sorts.add(name.getText());
    }
  }

  /**
   * This reads 0 or more function declarations, and stores each declaration both in the given
   * symbol map.
   *
   * Grammar: ( FUN IDENTIFIER type )
   */
  private void readDeclarations(LookupMap.Builder<ParserDeclaration> symbols) {
    while (true) {
      Token open = _status.readNextIf(AriTokenData.BRACKETOPEN);
      if (open == null) return;
      if (_status.readNextIf(AriTokenData.FUN) == null) {
        _status.pushBack(open);
        return;
      }
      // we have read: ( FUN.  Now the next parts have to be an IDENTIFIER and a type.
      Token name = _status.expect(AriTokenData.IDENTIFIER, "identifier (symbol name)");
      Type type = name == null ? null : readType();
      _status.expect(AriTokenData.BRACKETCLOSE, "closing bracket");
      if (name != null && type != null) {
        String n = name.getText();
        if (symbols.containsKey(n)) {
          _status.storeError(name, "Duplicate definition of function symbol " + n);
        }
        else symbols.put(n, new ParserDeclaration(name, n, type));
      }
    }
  }

  /**
   * This reads 0 or more rules, and stores each rule in the given rule builder.
   *
   * Grammar: ( RULE term term )
   */
  private void readRules(ImmutableList.Builder<ParserRule> rules) {
    Token ruletok;
    while (true) {
      Token open = _status.readNextIf(AriTokenData.BRACKETOPEN);
      if (open == null) return;
      ruletok = _status.readNextIf(AriTokenData.RULE);
      if (ruletok == null) {
        _status.pushBack(open);
        return;
      }
      // we have read: ( RULE.  Now the next parts have to be two terms and a closing bracket
      ParserTerm left = readTerm();
      ParserTerm right = readTerm();
      _status.expect(AriTokenData.BRACKETCLOSE, "closing bracket");

      LookupMap.Builder<ParserDeclaration> builder = new LookupMap.Builder<ParserDeclaration>();
      ParserRule rule = new ParserRule(ruletok, builder.build(), left, right);
      rules.add(rule);
    }
  }

  private ParserProgram readTRS() {
    LookupMap.Builder<ParserDeclaration> symbols = new LookupMap.Builder<ParserDeclaration>();
    ImmutableList.Builder<ParserRule> rules = ImmutableList.<ParserRule>builder();

    // read format line
    TrsFormat format = readFormat();
    if (format == null) return null;

    // read all the sorts
    _sorts = new TreeSet<String>();
    readSorts();
    
    // read all the declarations
    readDeclarations(symbols);

    // read all the rules
    readRules(rules);

    return new ParserProgram(symbols.build(), rules.build());
  }

  // ====================================== PUBLIC FUNCTIONS ======================================

  private static ParserProgram readProgram(TokenQueue queue, ErrorCollector collector) {
    ParsingStatus status =
      new ParsingStatus(queue, collector == null ? new ErrorCollector() : collector);
    AriParser parser = new AriParser(status);
    ParserProgram program = parser.readTRS();
    if (program != null) status.expect(Token.EOF, "end of input");
    if (collector == null || program == null) status.throwCollectedErrors();
    return program;
  }

  /**
   * Reads a full TRS from the given string, saving errors to the given collector.
   * @throws ParsingException
   */
  public static ParserProgram readProgramFromString(String str, ErrorCollector collector) {
    return readProgram(AriTokenData.getStringLexer(str), collector);
  }

  /**
   * Reads a full TRS from the given string, throwing a ParsingException if any are encountered.
   * @throws ParsingException
   */
  public static ParserProgram readProgramFromString(String str) {
    return readProgramFromString(str, null);
  }

  /**
   * Reads a full TRS from the given file, saving errors to the given collector.
   * @throws ParsingException
   */
  public static ParserProgram readProgramFromFile(String filename,
                                                  ErrorCollector coll) throws IOException {
    return readProgram(AriTokenData.getFileLexer(filename), coll);
  }
}

