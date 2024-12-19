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
 * A DeductionRule is a structure that can update the current proof state.
 * It may correspond either to a user-given or to an automatically generated command.
 */
abstract class DeductionRule {
  protected PartialProof _proof;
  protected OutputModule _module; // warning: might be null!

  /**
   * Generates a deduction rule that will manipulate proof states in the given partial proof.
   * Any printing will be done to the given output module.
   */
  protected DeductionRule(PartialProof proof, OutputModule module) {
    _proof = proof;
    _module = module;
  }

  /**
   * Generates a deduction rule that will manipulate proof states in the given partial proof.
   * No printing will be done to the given output module.
   */
  protected DeductionRule(PartialProof proof) {
    _proof = proof;
    _module = null;
  }

  /**
   * This executes a println to the underlying output module, provided one is set, and otherwise
   * does nothing.
   */
  protected void println(String str, Object ...objects) {
    if (_module != null) _module.println(str, objects);
  }

  /*
   * For consistency, every deduction rule is expected to define a method
   *   boolean apply(arg_1,...,arg_n)
   *
   * This method should execute the deduction rule on the current proof state (in the underlying
   * PartialProof), and return true if it applies (and changed the proof state), false if it didn't.
   * The application may have side effects both on the partial proof, and on the underlying
   * output module as explanations and failure messages are printed to it.
   *
   * We do not include this function as an abstract method, because argument counts may vary between
   * different instances of DeductionRule.
   */
}

