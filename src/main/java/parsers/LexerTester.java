/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsers;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.Token;

/**
 * This class is used to print the tokens in a given file.
 * This is primarily for testing purposes (beyond unit testing), but also to detect possible errors
 * in input files.
 * It is not used in the main program.
 */
public class LexerTester {
  private static void printToken(Token token) {
    String name = CoraLexer.VOCABULARY.getSymbolicName(token.getType());
    System.out.println(name + " " + token.getText());
  }

  private static void printLexerOutput(CoraLexer lexer) {
    int n = 0;
    while (true) {
      Token tk = lexer.nextToken();
      ArrayList<String> warnings = lexer.queryWarnings();
      int w = warnings.size();
      for ( ; n < w; n++) System.out.println(warnings.get(n));
      if (tk.getType() == Token.EOF) break;
      else printToken(tk);
    }
  }

  public static void printTokens(String filename) {
    try {
      ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
      CoraLexer lexer = new CoraLexer(input);
      printLexerOutput(lexer);
    }
    catch (IOException e) {
      System.out.println("Encountered IO exception: " + e.getMessage());
    }
  }
}

