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

import java.util.List;
import charlie.util.FixedList;
import cora.rwinduction.parser.CommandParsingStatus;

/** A base inherit for commands that do not take any arguments, providing shared functionality. */
abstract class SingularCommandInherit extends Command {
  @Override
  public final FixedList<String> callDescriptor() {
    return FixedList.of(queryName());
  }

  @Override
  public final List<TabSuggestion> suggestNext(String args) {
    return List.of(endOfCommandSuggestion());
  }

  @Override
  protected final boolean run(CommandParsingStatus status) {
    if (!status.commandEnded()) {
      return failure("Command " + queryName() + " should be invoked without any arguments.");
    }
    return run();
  }

  /** This is called when run is correctly invoked without any arguments. */
  protected abstract boolean run();
}

