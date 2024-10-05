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

import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TheoryFactory;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.config.Settings;
import cora.termination.transformation.CallByValueModifier;
import cora.termination.reduction_pairs.ReductionPairTerminationProver;
import cora.termination.reduction_pairs.horpo.Horpo;
import cora.termination.dependency_pairs.DPFramework;
import cora.termination.dependency_pairs.FullDPFramework;
import cora.termination.dependency_pairs.InnermostDPFramework;

import java.util.ArrayList;

public class TerminationHandler {
  /** Main access function for proving termination. */
  public static ProofObject proveTermination(TRS trs) {
    trs = updateTRSConstraints(trs);
    DPFramework framework = chooseFramework(trs, false);
    ProofObject po = framework.checkApplicable();
    if (po.queryAnswer() != ProofObject.Answer.YES) {
      ReductionPairTerminationProver prover = new ReductionPairTerminationProver(new Horpo(true));
      ProofObject ret = prover.proveTermination(trs);
      if (ret.queryAnswer() == ProofObject.Answer.YES) {
        return new WrapperProofObject(ret, trs, "termination");
      }
      return new WrapperProofObject(po, ret, trs, "termination", ProofObject.Answer.MAYBE);
    }
    return new WrapperProofObject(framework.run(), trs, "termination");
  }

  /** Main access function for proving universal computability. */
  public static ProofObject proveComputability(TRS trs) {
    trs = updateTRSConstraints(trs);
    DPFramework framework = chooseFramework(trs, true);
    return new WrapperProofObject(framework.run(), trs, "universal computability");
  }

  /**
   * Based on the reduction strategy and logical variables, we include all variables into the
   * constraints of the rules that we can assume will be instantiated by values.
   */
  private static TRS updateTRSConstraints(TRS trs) {
    if (Settings.queryRewritingStrategy().equals(Settings.Strategy.CallByValue) &&
        CallByValueModifier.isApplicable(trs)) {
      trs = CallByValueModifier.modify(trs);
    }
    return includeLVarInConstraint(trs);
  }

  /**
   * This function creates an updated TRS where all elements of LVar(l → r | φ) are included in
   * the constraint.  (The original TRS is unaffected.)
   * This allows any analysis to assume that the theory variables are exactly the elements of FV(φ).
   *
   * Made default instead of private only for the sake of unit testing.
   */
  static TRS includeLVarInConstraint(TRS trs) {
    ArrayList<Rule> rules = new ArrayList<Rule>(trs.queryRuleCount());
    boolean changed = false;
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rho = trs.queryRule(i);
      Term constraint = rho.queryConstraint();
      Term newconstraint = constraint;
      for (Variable x : rho.queryLVars()) {
        if (!constraint.vars().contains(x)) {
          Term eq = TheoryFactory.createEquality(x, x); 
          if (eq != null) newconstraint = TheoryFactory.createConjunction(newconstraint, eq);
        }
      }
      if (constraint == newconstraint) rules.add(rho);
      else {
        rules.add(TrsFactory.createRule(rho.queryLeftSide(), rho.queryRightSide(), newconstraint));
        changed = true;
      }
    }
    if (!changed) return trs;
    return trs.createDerivative(rules);
  }

  /** This selects the right DP Framework based on the settings and extra rules property */
  private static DPFramework chooseFramework(TRS trs, boolean extraRules) {
    return switch (Settings.queryRewritingStrategy()) {
      case Settings.Strategy.Innermost -> new InnermostDPFramework(trs, extraRules);
      case Settings.Strategy.CallByValue -> new InnermostDPFramework(trs, extraRules);
      case Settings.Strategy.Full -> new FullDPFramework(trs, extraRules);
    };
  }
}

class WrapperProofObject implements ProofObject {
  private TRS _trs;
  private Answer _answer;
  private String _property;
  private ProofObject _ob1;
  private ProofObject _ob2;

  private void setup(TRS trs, Answer answer, String property, ProofObject ob1, ProofObject ob2) {
    _trs = trs;
    _answer = answer;
    _property = property;
    _ob1 = ob1;
    _ob2 = ob2;
  }

  WrapperProofObject(ProofObject ob, TRS trs, String property) {
    setup(trs, ob.queryAnswer(), property, ob, null);
  }

  WrapperProofObject(ProofObject ob, TRS trs, String property, Answer answer) {
    setup(trs, answer, property, ob, null);
  }

  WrapperProofObject(ProofObject ob1, ProofObject ob2, TRS trs, String property, Answer answer) {
    setup(trs, answer, property, ob1, ob2);
  }

  public Answer queryAnswer() {
    return _answer;
  }

  public void justify(OutputModule module) {
    module.print("We consider %a of the ", _property);
    module.printTrs(_trs);
    _ob1.justify(module);
    if (_ob2 != null) _ob2.justify(module);
  }
}

