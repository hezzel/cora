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
import java.util.Set;
import java.util.List;
import org.jline.reader.Candidate;
import org.jline.reader.Completer;
import org.jline.reader.LineReader;
import org.jline.reader.LineReaderBuilder;
import org.jline.reader.ParsedLine;
import org.jline.terminal.Terminal;
import org.jline.terminal.TerminalBuilder;

import charlie.util.Pair;
import charlie.util.ExceptionLogger;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.command.Command;
import cora.rwinduction.command.CmdList;

/**
 * This class reads from console, but uses jline to support additional functionality, such as
 * tab completion and browsing previous commands.
 */
public class ReplInputter implements Inputter {
  private Terminal _terminal;
  private LineReader _lineReader;
  private BasicInputter _backup;

  public ReplInputter(CmdList cmds) {
    try {
      _terminal = TerminalBuilder.terminal();
      _lineReader = LineReaderBuilder.builder().terminal(_terminal)
        .completer(new ParameterCompleter(cmds))
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

class ParameterCompleter implements Completer {
  private CmdList _commands;

  ParameterCompleter(CmdList cmds) { _commands = cmds; }

  /**
   * Helper function for complete: this takes the parsed line, and splits it up into the first word
   * and the arguments that are already completed, NOT including the last word that the user is
   * still typing (since the given suggestions should give the full word, and not consider what has
   * been typed).
   */
  private Pair<String,String> split(ParsedLine p) {
    String sofar = p.line();
    int index = sofar.lastIndexOf(' ');
    if (index == -1) return new Pair<String,String>("", "");
    sofar = sofar.substring(0, index).trim();
    index = sofar.indexOf(' ');
    if (index == -1) return new Pair<String,String>(sofar, "");
    String cmd = sofar.substring(0, index);
    String args = sofar.substring(index + 1).trim();
    return new Pair<String,String>(cmd, args);
  }
  
  public void complete(LineReader r, ParsedLine p, List<Candidate> candidates) {
    Pair<String,String> parts = split(p);

    // first word: command name
    if (parts.fst().equals("")) {
      for (String cmd : _commands.queryCommands()) {
        candidates.add(new Candidate(cmd, cmd, "", null, "", cmd, true));
      }
      return;
    }

    // remainder: arguments
    Command cmd = _commands.queryCommand(parts.fst());
    if (cmd == null) return;
    List<Command.TabSuggestion> suggestions = cmd.suggestNext(parts.snd());
    for (Command.TabSuggestion option : suggestions) {
      String txt = option.text();
      String category = option.category();
      if (txt != null) candidates.add(new Candidate(txt, txt, category, null, "", txt, true));
      else if (suggestions.size() > 1) {
        candidates.add(new Candidate("", "", category, "<" + category + ">", "", category, true));
      }
      else candidates.add(new Candidate("", "", null, "<" + category + ">", "", category, true));
    }
  }
}

