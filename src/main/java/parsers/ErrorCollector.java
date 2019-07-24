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

import java.util.ArrayList;
import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import cora.exceptions.AntlrParserException;

public class ErrorCollector extends BaseErrorListener {
  private ArrayList<String> _messages;

  public ErrorCollector() {
    _messages = new ArrayList<String>();
  }

  @Override
  public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line,
                          int charPositionInLine, String msg, RecognitionException e) {
    _messages.add("" + line + ":" + charPositionInLine + ": " + msg);
  }

  public int queryErrorCount() {
    return _messages.size();
  }

  public String queryError(int index) {
    return _messages.get(index);
  }

  /**
   * If any errors have been collected, these are thrown using an AntlrParserException; then,
   * the list of messages is reset.
   * If no errors have been collected, nothing is done.
   */
  public void throwCollectedExceptions() throws AntlrParserException {
    if (_messages.size() == 0) return;
    AntlrParserException ex = new AntlrParserException(_messages);
    _messages = new ArrayList<String>();
    throw ex;
  }
}

