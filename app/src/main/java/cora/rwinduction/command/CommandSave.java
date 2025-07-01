/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.command;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

import charlie.util.FixedList;
import cora.io.OutputModule;
import cora.rwinduction.parser.CommandParsingStatus;

/**
 * The environment command :save, which saves the commands to get to the current proof state
 * to a file.
 */
public class CommandSave extends Command {
  @Override
  public String queryName() {
    return ":save";
  }

  @Override
  public FixedList<String> callDescriptor() {
    return FixedList.of(":save <file>");
  }

  @Override
  public void printHelp(OutputModule module) {
    module.println("Saves the history of the current state to a file, from which it can be " +
      "reloaded once you start a fresh proof attempt.");
  }

  @Override
  public ArrayList<TabSuggestion> suggestNext(String args) {
    ArrayList<TabSuggestion> ret = new ArrayList<TabSuggestion>();
    if (args.equals("")) ret.add(new TabSuggestion(null, "<filename>"));
    else ret.add(endOfCommandSuggestion());
    return ret;
  }

  @Override
  protected boolean run(CommandParsingStatus input) {
    String filename = input.readRest().trim();
    if (filename.length() > 2 && filename.charAt(0) == '"' &&
        filename.charAt(filename.length()-1) == '"') {
      filename = filename.substring(1, filename.length()-1);
    }
    if (filename.equals("")) {
      _module.println("Cannot save to an empty file.");
      return false;
    }
    ArrayList<String> commands = _proof.getCommandHistory();
    try {
      FileWriter filewriter = new FileWriter(filename, false);
      for (String cmd : commands) {
        filewriter.write(cmd);
        filewriter.write(System.lineSeparator());
      }
      filewriter.close();
      _module.println("%a commands written to %a.", commands.size(), filename);
    }
    catch (IOException e) {
      _module.println("Could not write to " + filename + ": %a.", e.getMessage());
    }
    return true;
  }
}

