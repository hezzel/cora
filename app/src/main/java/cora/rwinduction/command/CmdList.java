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
import java.util.TreeSet;
import cora.io.OutputModule;
import cora.rwinduction.engine.PartialProof;

/** A class to keep track of all commands by name, along with aliases. */
public final class CmdList {
  private TreeSet<String> _originals;
  private HashMap<String,Command> _commands;
  private PartialProof _proof;
  private OutputModule _module;

  public CmdList() {
    _originals = new TreeSet<String>();
    _commands = new HashMap<String,Command>();
    _proof = null;
    _module = null;
  }

  public void registerCommand(Command cmd) {
    String name = cmd.queryName();
    if (_commands.containsKey(name)) {
      throw new IllegalArgumentException("Double registration of command " + name + ".");
    }
    _commands.put(cmd.queryName(), cmd);
    _originals.add(cmd.queryName());
    if (_proof != null && _module != null) cmd.storeContext(_proof, _module);
  }

  /**
   * This stores "alias" as an alternative way to use the command identified by "original".  Note
   * that a command named original must be registered fist.
   */
  public void registerAlias(String alias, String original) {
    if (!_originals.contains(original)) {
      throw new IllegalArgumentException("Cannot register alias for " + original + " as there " +
        "is no command by that name defined.");
    }
    if (_commands.containsKey(alias)) {
      throw new IllegalArgumentException("Double registration of command " + alias +
        " (as alias).");
    }
    _commands.put(alias, _commands.get(original));
  }

  /**
   * Returns the set of all command names known to the parser.
   * This will only return the main commands; not the aliases.
   */
  public TreeSet<String> queryCommands() {
    return new TreeSet<String>(_originals);
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
    for (String name : _originals) _commands.get(name).storeContext(pp, module);
    _proof = pp;
    _module = module;
  }
}

