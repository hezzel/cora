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

package cora.rwinduction.parser;

import charlie.util.Either;
import charlie.util.FixedList;
import cora.rwinduction.engine.Command;

/**
 * A Syntax provides the technology to call a given command.  It handles the parsing, and can be
 * queried for the syntax that the user should use.
 */
public abstract class Syntax {
  /** The name of the command, so the primary way of invocation; e.g., :rules, simplify, ... */
  public abstract String queryName();

  /** Returns a FixedList of strings describing how to call the command. */
  public abstract FixedList<String> callDescriptor();

  /** Returns a description for the help command. */
  public abstract String helpDescriptor();

  /**
   * Parses the given string, and either yields a Command to execute it, or a string describing
   * why the string is not syntax-correct.
   *
   * Note: when the user invokes <command> <args>, the string this is called with is just the
   * <args> part, stripped of surrounding whitespace.  The function in this command is only called
   * if <command> is equal to queryName().
   */
  public abstract Either<String,Command> parse(String str);

  /** Helper function for inheriting classes: splits the command into words */
  protected String[] split(String command) {
    return command.trim().split("\\s+");
  }

  /** Helper function for inheriting classes: creates Left(str) */
  protected Either<String,Command> makeEither(String str) {
    return new Either.Left<String,Command>(str);
  }

  /** Helper function for inheriting classes: creates Right(cmd) */
  protected Either<String,Command> makeEither(Command cmd) {
    return new Either.Right<String,Command>(cmd);
  }

  public String toString() { return "Syntax: " + queryName(); }
}

