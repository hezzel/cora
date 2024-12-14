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

import java.util.HashMap;
import java.util.Set;
import charlie.util.Pair;
import charlie.util.Either;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;

/** A class to keep track of all commands by name. */
public final class CmdList {
  private HashMap<String,Command> _commands;
  private PartialProof _proof;
  private OutputModule _module;

  public CmdList() {
    _commands = new HashMap<String,Command>();
    _proof = null;
    _module = null;
  }

  public void registerCommand(Command cmd) {
    _commands.put(cmd.queryName(), cmd);
    if (_proof != null && _module != null) cmd.storeContext(_proof, _module);
  }

  /** Returns the set of all command names known to the parser. */
  public Set<String> queryCommands() {
    return _commands.keySet();
  }

  /** Returns the Command with the given name, or null if the name is unknown. */
  public Command queryCommand(String name) {
    return _commands.get(name);
  }

  /**
   * All Commands should be equipped with a context: a partial proof they operate in, and an
   * OutputModule they print information to.  This command sets the context for all Commands
   * registered in the CmdList, as well as all Commands that are added in the future.
   */
  public void storeContext(PartialProof pp, OutputModule module) {
    for (Command cmd : _commands.values()) cmd.storeContext(pp, module);
    _proof = pp;
    _module = module;
  }

  /**
   * IF the given string has the form <command> <args>, where <command> is a command that is known
   * to us (and <args> may be empty), then this returns LEFT(the pair of <command> and <args>).
   * Otherwise, it returns RIGHT(the <command> that is unknown).
   */
  public Either<Pair<Command,String>,String> parse(String str) {
    String cmd, rest;
    str = str.trim();
    int c = str.indexOf(' ');
    if (c == -1) { cmd = str; rest = ""; }
    else { cmd = str.substring(0, c); rest = str.substring(c+1).trim(); }
    Command command = _commands.get(cmd);
    if (command == null) return new Either.Right<Pair<Command,String>,String>(cmd);
    return new Either.Left<Pair<Command,String>,String>(new Pair<Command,String>(command, rest));
  }
}

