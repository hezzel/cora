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

package cora.termination.dependency_pairs.processors;

import cora.termination.dependency_pairs.Problem;

public interface Processor {
  /**
   * Returns false if we shouldn't even try to apply the processor on the given DP problem, for
   * example because it's a processor for unconstrained systems and the given problem has
   * constraints.
   */
  boolean isApplicable(Problem dpp);

  /**
   * Executes the processor on the given DP, and returns a proof object explaining either success
   * or failure.
   */
  ProcessorProofObject processDPP(Problem dpp);
}
