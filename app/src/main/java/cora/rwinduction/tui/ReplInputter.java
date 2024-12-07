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

package cora.rwinduction.tui;

import java.io.IOException;
import org.jline.reader.LineReader;
import org.jline.reader.LineReaderBuilder;
import org.jline.terminal.Terminal;
import org.jline.terminal.TerminalBuilder;
import org.jline.utils.InfoCmp;

import charlie.util.ExceptionLogger;

/**
 * This class reads from console, but uses jline to support additional functionality, such as
 * tab completion and browsing previous commands.
 */
public class ReplInputter implements Inputter {
  private Terminal _terminal;
  private LineReader _lineReader;
  private BasicInputter _backup;

  public ReplInputter() {
    try {
      _terminal = TerminalBuilder.terminal();
      _terminal.puts(InfoCmp.Capability.clear_screen);
      _lineReader = LineReaderBuilder.builder().terminal(_terminal)
        /*
        .completer(testCompleter)
        .highlighter(new DefaultHighlighter())
        .parser(new DefaultParser())
        */
        .build();
      _backup = null;
    }
    catch (IOException e) {
      ExceptionLogger.log("Could not create interactive terminal.  Please use the settings " +
        "to use the Basic inputter instead.", e);
      _terminal = null;
      _backup = new BasicInputter();
    }
  }

  public String readLine(String prompt) {
    if (_backup != null) return _backup.readLine(prompt);
    return _lineReader.readLine(prompt);
  }

  public void close() {
    try { _terminal.close(); }
    catch (IOException e) {
      ExceptionLogger.log("Could not close interactive terminal.", e);
    }
    _terminal = null;
  }
}

