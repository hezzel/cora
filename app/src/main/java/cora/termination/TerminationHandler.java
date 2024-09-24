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

package cora.termination;

import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.config.Settings;
import cora.termination.reduction_pairs.Horpo;
import cora.termination.dependency_pairs.FullDPFramework;

import java.util.Optional;

public class TerminationHandler {
  public static ProofObject proveTermination(TRS trs) {
    FullDPFramework dpF = new FullDPFramework();
    if (!Settings.isDisabled(dpF.queryDisabledCode())) return wrap(dpF.proveTermination(trs), trs);
    return Horpo.proveTermination(trs);
  }

  public static ProofObject proveComputability(TRS trs) {
    FullDPFramework dpF = new FullDPFramework();
    if (!Settings.isDisabled(dpF.queryDisabledCode())) {
      return wrap(dpF.proveComputability(trs), trs);
    }
    return new ProofObject() {
      public Answer queryAnswer() { return Answer.MAYBE; }
      public void justify(OutputModule o) {
        o.println("Dependency pairs were disabled, and this is currently the only appraoch " +
          "to prove universal/public computability.");
      }
    };
  }

  private static ProofObject wrap(ProofObject ob, TRS trs) {
    return new ProofObject() {
      public Answer queryAnswer() { return ob.queryAnswer(); }
      public void justify(OutputModule module) {
        module.print("We consider the ");
        module.printTrs(trs);
        ob.justify(module);
      }
    };
  }
}

