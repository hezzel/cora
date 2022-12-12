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

/** This is a grammar for the default Cora input format. */
lexer grammar CoraLexer;

@header {
package cora.parsers;

import java.util.ArrayList;
}

@lexer::members {
  private int comment_depth = 0;
  private String comment_start = "";
  private String string_start = "";
  private String string_so_far = "";

  private ArrayList<String> warnings = new ArrayList<String>();

  private String positionText(int pos) { return "" + getLine() + ":" + (pos+1); }

  private void reportError(int pos, String txt) {
    warnings.add(positionText(pos) + ": " + txt);
  }

  public ArrayList<String> queryWarnings() {
    return warnings;
  }
}

/* Lexer */

fragment IDCHAR     : ~[ \t\n\r{}()[\]",:/*] ;
fragment IDPART     : IDCHAR | '/'+ IDCHAR | '*'+ IDCHAR ;

fragment A          : 'a' | 'A' ;
fragment C          : 'c' | 'C' ;
fragment D          : 'd' | 'D' ;
fragment E          : 'e' | 'E' ;
fragment H          : 'h' | 'H' ;
fragment I          : 'i' | 'I' ;
fragment L          : 'l' | 'L' ;
fragment N          : 'n' | 'N' ;
fragment O          : 'o' | 'O' ;
fragment P          : 'p' | 'P' ;
fragment S          : 's' | 'S' ;
fragment R          : 'r' | 'R' ;
fragment T          : 't' | 'T' ;
fragment U          : 'u' | 'U' ;
fragment Y          : 'y' | 'Y' ;

WHITESPACE          : [ \t\r\n]+ -> skip ;

COMMENT             : '/*'
                    { comment_depth = 1;
                      comment_start = positionText(getCharPositionInLine()-2);
                      pushMode(INCOMMENT);
                      more();
                    } ;

ERRORStrayEndCom    : '*/'
                    { reportError(getCharPositionInLine()-2, "Unexpected closing comment */.");
                      skip();
                    } ;

BRACEOPEN           : '{' ;

BRACECLOSE          : '}' ;

BRACKETOPEN         : '(' ;

BRACKETCLOSE        : ')' ;

SQUAREOPEN          : '[' ;

SQUARECLOSE         : ']' ;

COMMA               : ',' ;

COLON               : ':' ;

DECLARE             : '::' ;

ARROW               : '-' '>' | '→' ;

TYPEARROW           : '=' '>' | '⇒' ;

INCLUDE             : I N C L U D E ;

SORT                : S O R T ;

OPERATOR            : O P E R A T O R ;

THEORY              : T H E O R Y ;

ALIAS               : A L I A S ;

TRANSLATE           : T R A N S L A T E ;

DISPLAY             : D I S P L A Y ;

CHAIN               : C H A I N ;

IDENTIFIER          : IDPART+ '/'* | IDPART+ '*'+ | '/'+ | '*'+ ;

ERRORIdEndCom       : IDPART* '*'+ '/'
                    { String ident = getText().substring(0, getText().length()-2);
                      reportError(getCharPositionInLine()-2, "Unexpected closing comment */ " +
                                                             "following identifier " + ident + ".");
                      setType(IDENTIFIER);
                      setText(ident);
                    } ;

IDENTIFIERWITHCOM   : IDPART* '/'+ '*'
                    { setType(IDENTIFIER);
                      String text = getText();
                      setText(text.substring(0,text.length()-2));
                      comment_depth = 1;
                      comment_start = positionText(getCharPositionInLine()-2);
                      pushMode(INCOMMENT);
                    } ;

QUOTE               : '"'
                    { string_start = positionText(getCharPositionInLine()-1);
                      pushMode(INSTRING);
                      more();
                    } ;

// ------------------------ dealing with (potentially recursive) comments -------------------------

mode INCOMMENT ;

CLOSE               : '*/'
                    { comment_depth--;
                      if (comment_depth == 0) {
                        popMode();
                        skip();
                      }
                      else more();
                    } ;

OPEN                : '/*'
                    { comment_depth++;
                      more();
                    } ;

ANYTHINGELSE        : . -> more ;

ERROREofInCom       : EOF
                    { popMode() ;
                      warnings.add(comment_start + ": Unterminated comment.");
                      skip();
                    } ;

// ------------------------------------- dealing with strings -------------------------------------

mode INSTRING ;

STRING              : '"'
                    { setText(string_so_far);
                      string_so_far = "";
                      popMode();
                    } ;

STRINGCONTENT       : (~[\n\r\\"])+
                    { string_so_far += getText();
                      more();
                    } ;

ESCAPEDNEWLINE      : ( ('\\' '\n' '\r' ) | ('\\' '\r' '\n') )
                    { string_so_far += "\n";
                      more();
                    } ;

ESCAPEDESCAPE       : ('\\' '\\')
                    { string_so_far += "\\";
                      more();
                    } ;

ESCAPEDQUOTE        : ('\\' '"')
                    { string_so_far += "\"";
                      more();
                    } ;

ERRORStringEof      : (EOF | ('\\' EOF))
                    { setType(STRING);
                      setText(string_so_far);
                      string_so_far = "";
                      warnings.add(string_start + ": String constant terminated by end of file.");
                      popMode();
                    } ;

ERRORstringNewline  : ('\n' | '\r')
                    { setType(STRING);
                      setText(string_so_far);
                      string_so_far = "";
                      warnings.add(string_start + ": String constant terminated by end of line.");
                      popMode();
                    } ;

ERROREscape         : '\\'
                    { reportError(getCharPositionInLine()-1, "Unexpected escape in string.");
                      more();
                    } ;

