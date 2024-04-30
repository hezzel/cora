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

package charlie.solvesmt;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingStatus;

/**
 * This class reads text from string or file written in the format of the SMTLIB.
 * For now, this is kept very simple, supporting only s-expressions, and no predefined symbols.
 */
class SmtParser {
  private ParsingStatus _status;

  /**
   * Stores the parsing status for use by methods of the SmtParser class.
   * Private because it should only be called by the static methods that use an SmtParser.
   */
  private SmtParser(ParsingStatus status) {
    _status = status;
  }

  // ==================================== READING S-EXPRESSIONS ===================================

  public SExpression readExpression() {
    Token tok = _status.readNextIf(SmtTokenData.NUMERAL);
    if (tok != null) {
      try { return new SExpression.Numeral(Integer.parseInt(tok.getText())); }
      catch (NumberFormatException e) {
        return new SExpression.Symbol(tok.getText());
          // likely a bigint or something, do what we can to avoid an unnecessary error
      }
    }
    tok = _status.readNextIf(SmtTokenData.IDENTIFIER);
    if (tok != null) return new SExpression.Symbol(tok.getText());
    tok = _status.readNextIf(SmtTokenData.BRACKETOPEN);
    if (tok != null) {
      List<SExpression> parts = readExpressions();
      _status.expect(SmtTokenData.BRACKETCLOSE, "closing bracket");
      return new SExpression.SExpList(parts);
    }
    tok = _status.nextToken();
    _status.storeError("Unexpected token: expected numeral, identifier or bracketed list.", tok);
    return new SExpression.Symbol(tok.getText());
  }

  public List<SExpression> readExpressions() {
    ArrayList<SExpression> ret = new ArrayList<SExpression>();
    while (!_status.peekNext().isEof() &&
           !_status.peekNext().getName().equals(SmtTokenData.BRACKETCLOSE)) {
      ret.add(readExpression());
    }
    return ret;
  }

  // ====================================== PUBLIC FUNCTIONS ======================================

  /**
   * Reads an S-expression from the given string.
   * @throws charlie.exceptions.ParseError
   */
  public static SExpression readExpressionFromString(String str) {
    ParsingStatus status = new ParsingStatus(SmtTokenData.getStringLexer(str), 1);
    SmtParser parser = new SmtParser(status);
    SExpression ret = parser.readExpression();
    status.expect(Token.EOF, "end of input");
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Reads a list of S-expressions from the given string.
   * @throws charlie.exceptions.ParseError
   */
  public static List<SExpression> readExpressionsFromString(String str) {
    ParsingStatus status = new ParsingStatus(SmtTokenData.getStringLexer(str), 1);
    SmtParser parser = new SmtParser(status);
    List<SExpression> ret = parser.readExpressions();
    status.expect(Token.EOF, "end of input");
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Reads a list of S-expressions from the given file.
   * @throws charlie.exceptions.ParseError
   */
  public static List<SExpression> readExpressionsFromFile(String filename) throws IOException {
    ParsingStatus status = new ParsingStatus(SmtTokenData.getFileLexer(filename), 1);
    SmtParser parser = new SmtParser(status);
    List<SExpression> ret = parser.readExpressions();
    status.expect(Token.EOF, "end of file");
    status.throwCollectedErrors();
    return ret;
  }
}

