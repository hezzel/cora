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

package cora.io;

/**
 * A ProofObject is the way that some method within Cora passes its result to the calling function.
 * A ProofObject provides an answer, and can prints the justification for this answer.  In the
 * future, it may also be able to print a formal proof for automatic certification.
 * (The justification is allowed to be empty, for example if the answer is something like MAYBE.)
 */
public interface ProofObject {
  /**
   * The answer to be given depends on the kind of proof object.  Typically, this would return
   * YES, NO or MAYBE in some enum type, but if we are for instance analysing complexity, it might
   * return something like "O(n)"; and for reduction it would return the normal form of an input
   * term.
   */
  Object queryAnswer();

  /**
   * If an answer is given, we should be able to prove it.  This may be empty, if the answer given
   * is "MAYBE" (or some other way of saying "we don't know"), but it could also be quite elaborate.
   * The ProofObject can print itself to an OutputModule.
   *
   * Note: any implementing object should support OutputModules with a Plain style.  If an
   * OutputModule with an unsupported style is given, the implementing ProofObject should default
   * to Plain.
   */
  void justify(OutputModule out);
}

