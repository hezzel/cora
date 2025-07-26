/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

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

import java.util.ArrayList;

import charlie.util.FixedList;
import charlie.util.LookupMap;
import charlie.types.*;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingStatus;

/**
 * The FirstOrderParser is an abstract base class for parsers that read first-order terms and rules
 * following the old TPDB format.  Mostly, it is designed to handle shared functionality between the
 * FirstOrderParser and the ITrsParser classes.
 */
abstract class FirstOrderParser implements Parser {
  private String IDENTIFIER, BRACKETOPEN, BRACKETCLOSE, COMMA, ARROW,
                 RULESDECSTART, VARSDECSTART, COMMENTSTART;

  /**
   * The parser keeps track of the status of parser so far; all read functions have a (potential)
   * side effect of advancing the parsing status.
   */
  protected final ParsingStatus _status;

  /** Stores the parsing status, and the token names that we will need for parsing. */
  protected FirstOrderParser(ParsingStatus status, String ident, String bopen, String bclose,
      String comma, String arrow, String rulesstart, String varsstart, String comstart) {
    _status = status;
    IDENTIFIER = ident;
    BRACKETOPEN = bopen;
    BRACKETCLOSE = bclose;
    COMMA = comma;
    ARROW = arrow;
    RULESDECSTART = rulesstart;
    VARSDECSTART = varsstart;
    COMMENTSTART = comstart;
  }

  protected abstract boolean isSectionStart(Token token);

  // ======================================== READING TERMS =======================================

  protected abstract ParserTerm readTerm();

  /**
   * term ::= IDENTIFIER
   *        | IDENTIFIER BRACKETOPEN BRACKETCLOSE
   *        | IDENTIFIER BRACKETOPEN term (COMMA term)* BRACKETCLOSE
   *
   * If an error is encountered, error recovery is done if possible (for example, missing brackets
   * may be filled in).  In this case, the term will be marked as containing Errors.
   */
  protected ParserTerm readFirstOrderTerm() {
    // first we should have an IDENTIFIER
    Token start = _status.expect(IDENTIFIER, "an identifier (variable or function name)");
    if (start == null) return null;
    ParserTerm head = new Identifier(start, start.getText());
    // if we don't follow up with a BRACKETOPEN, then that's enough
    if (_status.readNextIf(BRACKETOPEN) == null) return head;
    // if we follow the BRACKETOPEN with a BRACKETCLOSE, then that's enough
    if (_status.readNextIf(BRACKETCLOSE) != null) {
      return new Application(start, head, FixedList.of());
    }
    // otherwise, start reading recursively
    FixedList.Builder<ParserTerm> builder = new FixedList.Builder<ParserTerm>();
    ArrayList<ParserTerm> args = new ArrayList<ParserTerm>();
    boolean errored = false;
    while (true) {
      ParserTerm child = readTerm();
      if (child == null) errored = true;
      else builder.add(child);
      // if we encounter BRACKETCLOSE, we have finished this term
      if (_status.readNextIf(BRACKETCLOSE) != null) break;
      // otherwise we must encounter COMMA followed by at least one more term
      if (_status.expect(COMMA, "a comma or closing bracket") == null) {
        // error situation: if they may have just forgotten a comma, pretend we saw one and
        // continue, but otherwise return what we already have
        errored = true;
        if (!_status.nextTokenIs(IDENTIFIER)) break;
      }
    }
    ParserTerm ret = new Application(start, head, builder.build());
    if (errored) return new PErr(ret);
    else return ret;
  }

  // ======================================== READING RULES =======================================

  protected abstract ParserRule readRule(LookupMap<ParserDeclaration> vars);

  /**
   * rules ::= RULESDECSTART rule* BRACKETCLOSE
   *
   * The current status is expected to start with RULESDECSTART (if not, we store an error and
   * return the empty list).  We read and return the rules, or throw a ParseError if the rules list
   * is poorly shaped.
   *
   * If any variables have already been declared, these are passed in the argument list, to be
   * stored as part of the rule.  (This map is allowed to be empty, but not null.)
   */
  protected FixedList<ParserRule> readRules(LookupMap<ParserDeclaration> declaredVars) {
    FixedList.Builder<ParserRule> ret = new FixedList.Builder<ParserRule>();
    if (_status.expect(RULESDECSTART, "rules declaration") == null) {
      return ret.build();
    }
    while (_status.readNextIf(BRACKETCLOSE) == null) {
      ParserRule r = readRule(declaredVars);
      if (r != null) ret.add(r);
    }
    return ret.build();
  }

  // ===================================== READING DECLARATIONs ===================================

  /**
   * varlist ::= VARSDECSTART IDENTIFIER* BRACKETCLOSE
   *
   * When presented with a varlist, this function saves all the variables into the returned
   * mapping, with the default sort as their type (since varlists can only occur in UNSORTED TRSs).
   * When presented with anything else, it returns null (and does not read anything).
   */
  protected LookupMap<ParserDeclaration> readVarList() {
    Token start = _status.readNextIf(VARSDECSTART);
    if (start == null) return null;
    LookupMap.Builder<ParserDeclaration> ret = new LookupMap.Builder<ParserDeclaration>();
    while (true) {
      Token next = _status.nextToken();
      if (next.getName().equals(BRACKETCLOSE)) return ret.build();
      if (next.getName().equals(IDENTIFIER)) {
        String name = next.getText();
        if (ret.containsKey(name)) {
          _status.storeError(next, "Double declaration of variable " + name);
        }
        else ret.put(name, new ParserDeclaration(next, name, TypeFactory.defaultSort));
      }
      else {
        // error handling for incorrect tokens
        if (next.isEof()) {
          _status.storeError(start, "Encountered end of input while reading varlist; no closing " +
                                    "bracket given.");
          return ret.build();
        }
        if (isSectionStart(next)) {
          _status.storeError(next, "Unexpected " + next.getText() + " while reading varlist; " +
            "did you forget a closing bracket?");
          _status.pushBack(next);
          return ret.build();
        }
        // if we encounter something else, it's unclear what the programmer did, so let's just
        // abort the parsing process
        _status.abort(next, "Unexpected token: " + next.getText() + " (" + next.getName() +
          "); expected a variable name");
      }
    }
  }

  /**
   * comment ::= COMMENTOPEN string BRACKETCLOSE EOF
   * If the current status starts with COMMENTOPEN, we read until the end of the file and store an
   * error if the last bracket is not right before it; in this case we return true.
   * If it starts with something else, we return false and read nothing.
   */
  protected boolean readComment() {
    Token start = _status.readNextIf(COMMENTSTART);
    if (start == null) return false;
    Token token = _status.nextToken();
    Token lastFollow = null;
    while (!token.isEof()) {
      if (token.getName().equals(BRACKETCLOSE)) {
        lastFollow = _status.nextToken();
        if (lastFollow.isEof()) return true;
      }
      token = _status.nextToken();
    }
    if (lastFollow == null) _status.storeError(start, "Unclosed comment.");
    else _status.storeError(lastFollow, "Unexpected token: " + lastFollow.getText() +
      "; expected end of input following comment.");
    return true;
  }
}

