/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

  private String getUnicodeSubstring(String txt, int pos) {
    if (pos >= txt.length()) return null;
    if (txt.charAt(pos) == '{') {
      for (int i = pos + 1; i < txt.length(); i++) {
        if (txt.charAt(i) == '}') return txt.substring(pos, i+1);
      }
      return null;
    }
    if (pos + 4 > txt.length()) return null;
    return txt.substring(pos, pos + 4);
  }

  private String doTranslate(String unicode) {
    if (unicode.charAt(0) == '{') unicode = unicode.substring(1, unicode.length()-1);
    int code = 0;
    for (int i = 0; i < unicode.length(); i++) {
      char c = unicode.charAt(i);
      code = code * 16 + (int)c;
      if ('0' <= c && c <= '9') code -= (int)'0';
      else if ('a' <= c && c <= 'f') code += 10 - (int)'a';
      else if ('A' <= c && c <= 'F') code += 10 - (int)'A';
      else return null;
    }
    return "" + (char)code;
  }

  private String translateUnicode(String txt, Token tok) {
    StringBuilder builder = new StringBuilder();
    int i = 0;
    while (i < txt.length()) {
      int j = txt.indexOf("\\u", i);
      if (j == -1) {
        builder.append(txt.substring(i));
        return builder.toString();
      }
      builder.append(txt.substring(i, j));
      String unistring = getUnicodeSubstring(txt, j + 2);
      String transl = unistring == null || unistring.length() == 0 ? null : doTranslate(unistring);
      if (transl == null) {
        _status.storeError(tok, "Poorly formed string constant: " + txt.substring(j));
        return builder.toString();
      }
      builder.append(transl);
      i = j + 2 + unistring.length();
    }
    return builder.toString();
  }

  public SExpression readExpression() {
    Token tok = _status.readNextIf(SmtTokenData.NUMERAL);
    if (tok != null) {
      try { return new SExpression.Numeral(Integer.parseInt(tok.getText())); }
      catch (NumberFormatException e) {
        return new SExpression.Symbol(tok.getText());
          // likely a bigint or something, do what we can to avoid an unnecessary error
      }
    }
    tok = _status.readNextIf(SmtTokenData.STRING);
    if (tok != null) return new SExpression.StringConstant(translateUnicode(tok.getText(), tok));
    tok = _status.readNextIf(SmtTokenData.IDENTIFIER);
    if (tok != null) return new SExpression.Symbol(tok.getText());
    tok = _status.readNextIf(SmtTokenData.BRACKETOPEN);
    if (tok != null) {
      List<SExpression> parts = readExpressions();
      _status.expect(SmtTokenData.BRACKETCLOSE, "closing bracket");
      return new SExpression.SExpList(parts);
    }
    tok = _status.nextToken();
    _status.storeError(tok, "Unexpected token: expected numeral, identifier or bracketed list.");
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
   * @throws charlie.exceptions.ParseException
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
   * @throws charlie.exceptions.ParseException
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
   * @throws charlie.exceptions.ParseException
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

