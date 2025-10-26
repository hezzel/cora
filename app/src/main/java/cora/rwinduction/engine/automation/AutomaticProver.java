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

package cora.rwinduction.engine.automation;

import java.util.ArrayList;
import java.util.Optional;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.PartialProof;

/**
 * This class organises the automatic reasoning abilities of the rewriting inducter.
 */
public final class AutomaticProver {
  /**
   * This function does obvious steps on the top goal: simplifying, calculating, and various ways
   * of deleting.
   */
  public static ArrayList<DeductionStep> handleBasics(PartialProof proof) {
    // simplify as far as we can
    ArrayList<DeductionStep> ret = AutoSimplifier.simplifyFully(proof);
    // if we can finish off by deleting, do so
    DeductionStep step = AutoDeleter.tryDeleteTopEquation(proof);
    if (step != null && step.execute(proof, Optional.empty())) {
      ret.add(step);
      return ret;
    }
    // TODO: context
    return ret;
  }
}

