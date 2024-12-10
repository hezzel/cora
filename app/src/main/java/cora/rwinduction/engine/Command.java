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
 * A Command either gives information to the user, or updates the ProverContext, to correspond with
 * a user-generated or generated command.
 */
public interface Command {
  /** This returns a syntax that could be used to create the current Command instance. */
  String callDescriptor();
  /** This executes the Command. */
  void run(ProverContext context, OutputModule module);
}

