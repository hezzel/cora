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
 * A DeductionRule is a structure that can update the current proof state.  It may correspond either
 * to a user-given or to an automatically generated command.
 */
public interface DeductionRule {
  /**
   * This executes the deduction rule on the proof state, and returns true if it applies (and
   * changed the proof state), false if it didn't.  The given module is used for a potential
   * response from the command, in particular to provide an explanation if the deduction rule does
   * not apply.
   */
  boolean apply(PartialProof proof, OutputModule module);

  /**
   * This executes the deduction rule on the proof state, and returns true if it applies (and
   * changed the proof state), false if it didn't.  Nothing is printed.
   */
  default boolean apply(PartialProof proof) { return apply(proof, null); }
}

