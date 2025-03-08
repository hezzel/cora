/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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

import java.util.Optional;

import charlie.util.FixedList;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.CommandParsingStatus;

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
   * Given that input represents the input given by the user, with reader head pointed just after
   * the command name (which must necessarily correspond to the current command), this continues
   * parsing the input.  If the input indeed describes a correct invocation of the current Command,
   * it executes the Command.  If it does not, the underlying OutputModule is updated with a
   * description why the command failed, both if it's a syntax failure or if the command defines a
   * deduction rule that is not applicable.  The return value indicates whether the invocation was
   * succesful or not.
   *
   * Note: the context (PartialProof and OutputModule) MUST be set before calling execute; otherwise
   * a RuntimeException will be thrown.
   *
   * Usage note: when the user invokes <command> <args>, this function should be called with
   * input a command status representing the full string, but reader head pointed at the <args>
   * part.
   */
  public final boolean execute(CommandParsingStatus input) {
    if (_proof == null || _module == null) {
      throw new RuntimeException("Command " + queryName() + " was called without the context " +
        "being set!");
    }
    return run(input);
  }

  /**
   * All inheriting classes should implement this.  This method implements the execute function,
   * and may assume that _proof and _module have already been set.
   */
  protected abstract boolean run(CommandParsingStatus input);

  /**
   * Helper function for inheriting classes: prints the given message to the underlying output
   * module and returns false.
   */
  protected final boolean failure(String mess) {
    _module.println("%a", mess);
    return false;
  }

  /**
   * Helper function for inheriting classes: if the command on input has ended this simply returns
   * true, otherwise it prints an error message and returns false.
   */
  protected final boolean verifyEnded(CommandParsingStatus input) {
    if (input.commandEnded()) return true;
    _module.println("Unexpected argument at position %a: expected end of command.",
      input.currentPosition());
    return false;
  }

  /** Returns _module wrapped in an Optional, as deduction steps often need. */
  protected final Optional<OutputModule> optionalModule() {
    return Optional.of(_module);
  }

  public final String toString() { return "Command: " + queryName(); }
}

