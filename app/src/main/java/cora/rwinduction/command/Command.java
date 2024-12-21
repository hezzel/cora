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

package cora.rwinduction.command;

import charlie.util.Pair;
import charlie.util.FixedList;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;

/**
 * A Command is an action that the user can call within the interactive prover.
 * The class handles the parsing and execution of the user's command, and it can be queried for the
 * syntax that the user should use.
 */
public abstract class Command {
  protected PartialProof _proof;
  protected OutputModule _module;

  /**
   * Creates a Command, and sets up the PartialProof and OutputModule that this command will work
   * on.
   */
  protected Command(PartialProof pp, OutputModule om) {
    _proof = pp;
    _module = om;
  }

  /**
   * Creates a Command without pre-set PartialProof and OutputModule.  These must still be set
   * using storeContext before execute() is called.
   */
  protected Command() {
    _proof = null;
    _module = null;
  }

  /**
   * A Command, when executed, typically needs an OutputModule, and often also a PartialProof.
   * This is the context in which the command operates.  Hence, these need to be known before
   * execute() is called.
   */
  public final void storeContext(PartialProof pp, OutputModule om) {
    _proof = pp;
    _module = om;
  }

  /** The name of the command, so the primary way of invocation; e.g., :rules, simplify, ... */
  public abstract String queryName();

  /** Returns a FixedList of strings describing how to call the command. */
  public abstract FixedList<String> callDescriptor();

  /** Returns a description for the help command. */
  public abstract String helpDescriptor();

  /**
   * This parses the given string, and if it describes a correct invocation of the current Command,
   * it executes the command.  If not, the underlying OutputModule is updated with a description why
   * the command failed, both if it's a syntax failure or if the command defines a deduction rule
   * that is not applicable.  The return value indicates whether the invocation was succesful or
   * not.
   *
   * Note: the context (PartialProof and OutputModule) MUST be set before calling execute; otherwise
   * a RuntimeException will be thrown.
   *
   * Note: when the user invokes <command> <args>, this function should be called with just the
   * <args> part, stripped of surrounding whitespace.  It should only be called when <command> is
   * equal to queryName().
   */
  public final boolean execute(String str) {
    if (_proof == null || _module == null) {
      throw new RuntimeException("Command " + queryName() + " was called without the context " +
        "being set!");
    }
    return run(str);
  }

  /**
   * All inheriting classes should implement this.  This method implements the execute function,
   * and may assume that _proof and _module have already been set.
   */
  protected abstract boolean run(String str);

  /**
   * Helper function for inheriting classes: splits the text into the first word, and the rest.
   */
  protected final Pair<String,String> splitWord(String text) {
    text = text.trim();
    int k = text.indexOf(' ');
    if (k == -1) return new Pair<String,String>(text, "");
    return new Pair<String,String>(text.substring(0, k), text.substring(k+1).trim());
  }

  /**
   * Helper function for inheriting classes: prints the given message to the underlying output
   * module and returns false.
   */
  protected final boolean failure(String mess) {
    _module.println("%a", mess);
    return false;
  }

  public final String toString() { return "Command: " + queryName(); }
}

