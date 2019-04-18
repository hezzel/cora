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

import org.junit.Test;
import static org.junit.Assert.*;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import java.util.ArrayList;
import cora.parsers.CoraLexer;

public class CoraLexerTest {
  private CoraLexer createLexer(String str) {
    return new CoraLexer(CharStreams.fromString(str));
  }

  private ArrayList<Token> tokenise(String str) {
    CoraLexer lexer = createLexer(str);
    ArrayList<Token> ret = new ArrayList<Token>();
    while (true) {
      Token tk = lexer.nextToken();
      if (tk.getType() == Token.EOF) break;
      ret.add(tk);
    }
    return ret;
  }

  @Test
  public void testLexSimpleIdentifier() {
    ArrayList<Token> parts = tokenise("myfun");
    assertTrue(parts.size() == 1);
    assertTrue(parts.get(0).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(0).getText().equals("myfun"));
  }

  /*
  @Test
  public void testLexUnicodeIdentifier() {
    ArrayList<Token> parts = tokenise("émy∀fun");
    assertTrue(parts.size() == 1);
    assertTrue(parts.get(0).getType() == CoraLexer.IDENTIFIER);
    assertTrue(parts.get(0).getText().equals("émy∀fun"));
  }
  */
}

