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

import java.util.Optional;

import charlie.exceptions.ParseException;
import charlie.util.Pair;
import charlie.util.FixedList;
import charlie.parser.lib.ParsingStatus;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.parser.RWParser;

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
   * Given that status represents the parsing status of reading a command AFTER having read the
   * command name that corresponds to the current command, this continues parsing the input.  If
   * the input indeed describes a correct invocation of the current Command, it executes the
   * Command.  If it does not, the underlying OutputModule is updated with a description why the
   * command failed, both if it's a syntax failure or if the command defines a deduction rule that
   * is not applicable.  The return value indicates whether the invocation was succesful or not.
   *
   * Note: the context (PartialProof and OutputModule) MUST be set before calling execute; otherwise
   * a RuntimeException will be thrown.
   *
   * Note: when the user invokes <command> <args>, this function should be called with status
   * pointing at the <args> parts.
   */
  public final boolean execute(ParsingStatus status) {
    if (_proof == null || _module == null) {
      throw new RuntimeException("Command " + queryName() + " was called without the context " +
        "being set!");
    }
    try { return run(status); }
    catch (ParseException e) {
      _module.println("Parse error at %a", e.getMessage().trim());
      return false;
    }
  }

  /**
   * All inheriting classes should implement this.  This method implements the execute function,
   * and may assume that _proof and _module have already been set.  It is perfectly okay for run
   * to ignore ParseExceptions; these will be caught and printed by execute.
   */
  protected abstract boolean run(ParsingStatus status);

  /**
   * Helper function for inheriting classes: this returns whether the status is currently pointing
   * to the end of a command (i.e., the next token is EOF).
   */
  protected final boolean commandEnds(ParsingStatus status) {
    return status.peekNext().isEof() ||
           status.peekNext().getName().equals(RWParser.SEPARATOR);
  }

  /**
   * Helper function for inheriting classes: prints the given message to the underlying output
   * module and returns false.
   */
  protected final boolean failure(String mess) {
    _module.println("%a", mess);
    return false;
  }

  /** Returns _module wrapped in an Optional, as deduction steps often need. */
  protected final Optional<OutputModule> optionalModule() {
    return Optional.of(_module);
  }

  public final String toString() { return "Command: " + queryName(); }
}

