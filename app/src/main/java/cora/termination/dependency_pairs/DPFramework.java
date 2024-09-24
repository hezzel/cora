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

package cora.termination.dependency_pairs;

import charlie.trs.TRS;
import charlie.trs.TrsProperties.*;
import cora.io.OutputModule;
import cora.io.ProofObject;

public class DPFramework {
  public static String queryDisabledCode() {
    return "dp";
  }

  public static String queryPrivateDisabledCode() {
    return "private";
  }

  private ProofObject isTRSApplicable(TRS trs) {
    if (!trs.verifyProperties(Level.APPLICATIVE, Constrained.YES, Products.DISALLOWED,
                              Lhs.PATTERN, Root.THEORY)) {
      return new ProofObject() {
        public Answer queryAnswer() { return Answer.MAYBE; }
        public void justify(OutputModule o) {
          o.println("For now, static dependency pairs can only be applied on applicative " +
                    "systems without tuples, where the left-hand sides of rules are patterns " +
                    "of the form f(l1,...,lk) with f a function symbol.");
        }
      };
    }
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    return checker.checkAccessibility();
  }
}

