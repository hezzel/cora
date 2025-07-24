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

package cora.rwinduction;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Scanner;

import charlie.util.FixedList;
import charlie.parser.lib.ParsingException;
import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.EquationParser;
import cora.rwinduction.parser.CommandParsingStatus;
import cora.rwinduction.command.CmdList;
import cora.rwinduction.command.DeductionCommand;

/**
 * The SaveFile class represents a file that the user has saved to store a proof trace.
 * It can be used to restore the given position in a proof.
 */
public class SaveFile {
  private String _filename;
  private TRS _trs;
  private CmdList _cmds;
  private OutputModule _output;

  /**
   * Sets up the class to parse the given file, using the given commands and trs, and printing
   * possible error messages to the given output module.
   *
   * Note: since a savefile contains the equations that we need to start the proof state from, the
   * cmds variable does NOT have its context stored yet.  Doing so is a responsiblity of this
   * class, when read() is called.
   */
  public SaveFile(String filename, TRS trs, CmdList cmds, OutputModule output) {
    _filename = filename;
    _trs = trs;
    _cmds = cmds;
    _output = output;
  }

  /**
   * This reads the underlying file, which is expected to first lists a number of equation contexts
   * (marked GOAL), followed by a number of commands.  The equation contexts are parsed and
   * returned; the commands are stored into the list commands.  If there are problems reading the
   * file, or any of the equation contexts are not valid, an appropriate error message is printed
   * to the output module and null is returned.
   */
  private FixedList<EquationContext> readEquations(ArrayList<String> commands) {
    FixedList.Builder<EquationContext> builder = new FixedList.Builder<EquationContext>();
    boolean readAny = false;
    try {
      Scanner s = new Scanner(new File(_filename));
      while (s.hasNextLine()) {
        String line = s.nextLine();
        if (line.length() > 6 && line.substring(0,6).equals("GOAL E")) {
          EquationContext goal = readGoal(line);
          if (goal == null) return null;
          builder.add(goal);
          readAny = true;
        }
        else commands.add(line);
      }
      s.close();
    }   
    catch (IOException e) {
      _output.println("Could not read from file %a: %a.", _filename, e.getMessage());
      return null;
    }
    if (!readAny) {
      _output.println("No goals are given in input file %a.", _filename);
      return null;
    }
    return builder.build();
  }

  /**
   * Reads a goal of the form: GOAL E<index>: <equation context>.  If any parsing issues arise, an
   * error message is printed to the output module and null returned instead.
   */
  private EquationContext readGoal(String line) {
    int k = line.indexOf(':');
    if (k == -1) {
      _output.println("Illegal input line (not of the form GOAL E<number>: <rest>): %a", line);
      return null;
    }
    int id = -1; 
    try { id = Integer.parseInt(line.substring(6, k)); }
    catch (NumberFormatException e) {
      _output.println("Illegal input line (E is not followed by <integer><colon>): %a", line);
      return null;
    }   
    try {
      EquationContext ec = EquationParser.parseEquationContext(line.substring(k+1), id, _trs);
      if (ec != null) return ec;
      _output.println("Invalid equation context: %a", line);
    }   
    catch (ParsingException e) {
      _output.println("Illegal input line [%a]: %a", line, e.getMessage());
    }   
    return null;
  }

  /**
   * This executes the given command, using the underlying command list.
   * If successful, true is returned; if not, an error message is printed and false is returned.
   */
  private boolean runCommand(String str) {
    CommandParsingStatus status = new CommandParsingStatus(str);
    while (!status.done()) {
      String cmdname = status.nextWord();
      if (cmdname == null) {
        _output.println("Illegal input: %a", str);
        return false;
      }
      DeductionCommand cmd = _cmds.queryDeductionCommand(cmdname);
      if (cmd == null) {
        _output.println("Unknown deduction command: %a.", cmdname);
        return false;
      }
      if (!cmd.executeWithoutVerification(status)) return false;
      if (!status.done()) {
        int pos = status.currentPosition();
        _output.println("Error parsing command [%a]: unexpected token %a at position %a, where " +
          "the end of the command was expected.", str, status.nextWord(), pos);
        return false;
      }
    }
    return true;
  }

  /**
   * This reads the savefile and replays the proof steps (omitting any expensive checks), ending up
   * with a partial proof status (which still has a history).  If anything goes wrong, an error
   * message is printed on the underlying output module, and null is returned.
   */
  public PartialProof restore() {
    ArrayList<String> commands = new ArrayList<String>();
    FixedList<EquationContext> eqs = readEquations(commands);
    if (eqs == null) return null;
    PartialProof proof = new PartialProof(_trs, eqs, lst -> _output.generateUniqueNaming(lst));
    _cmds.storeContext(proof, _output);
    for (String cmd : commands) {
      if (!runCommand(cmd)) return null;
    }
    return proof;
  }
}

