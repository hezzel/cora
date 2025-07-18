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
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.ProofState;
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
    String history = storeHistory();
    try {
      FileWriter filewriter = new FileWriter(filename, false);
      filewriter.write(history);
      filewriter.close();
      _module.println("Original equations and command history have been written to %a.", filename);
    }
    catch (IOException e) {
      _module.println("Could not write to %a: %a.", filename, e.getMessage());
    }
    return true;
  }

  /**
   * Does the main work for run, printing the history to the given string.
   * Default rather than private for the sake of unit testing.
   */
  String storeHistory() {
    Printer pp = PrinterFactory.createParseablePrinter(_proof.getContext().getTRS());
    printGoals(pp);
    printCommands(pp);
    return pp.toString();
  }

  private void printGoals(Printer printer) {
    ProofState firstState;
    if (_proof.getDeductionHistory().size() > 0) {
      firstState = _proof.getDeductionHistory().get(0).getOriginalState();
    }
    else firstState = _proof.getProofState();
    for (EquationContext ec : firstState.getEquations()) {
      printer.add("GOAL ");
      ec.print(printer);
      printer.add(System.lineSeparator());
    }
  }

  private void printCommands(Printer printer) {
    ArrayList<String> commands = _proof.getCommandHistory();
    for (String cmd : commands) {
      printer.add(cmd);
      printer.add(System.lineSeparator());
    }
  }
}

