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

package cora.rwinduction.engine;

import cora.io.OutputModule;

/**
 * A Command either gives information to the user, or updates a PartialProof, to correspond with
 * a user-given or automatically generated command.
 */
public interface Command {
  /**
   * This executes the Command.  The given module is used for a potential response from the command,
   * for example if a deduction rule does not apply, or to provide the information requested by an
   * environment command like :rules.
   */
  void run(PartialProof proof, OutputModule module);
}

