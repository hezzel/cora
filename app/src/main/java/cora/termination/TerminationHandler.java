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
import cora.termination.reduction_pairs.Horpo;
import cora.termination.dependency_pairs.DPFramework;
import cora.termination.dependency_pairs.FullDPFramework;

import java.util.ArrayList;

public class TerminationHandler {
  /** Main access function for proving termination. */
  public static ProofObject proveTermination(TRS trs) {
    trs = updateTRSConstraints(trs);
    DPFramework framework = chooseFramework(trs, true);
    ProofObject po = framework.checkApplicable();
    if (po.queryAnswer() != ProofObject.Answer.YES) {
      ProofObject ret = Horpo.proveTermination(trs);
      if (ret.queryAnswer() == ProofObject.Answer.YES) return wrap(ret, trs, "termination");
      else return wrap(po, ret, trs, "termination");

    }
    return wrap(framework.run(), trs, "termination");
  }

  /** Main access function for proving universal computability. */
  public static ProofObject proveComputability(TRS trs) {
    trs = updateTRSConstraints(trs);
    DPFramework framework = chooseFramework(trs, true);
    return wrap(framework.run(), trs, "universal computability");
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
    return new FullDPFramework(trs, extraRules);
  }

  /** Improve the justification in a proof by printing the TRS first. */
  private static ProofObject wrap(ProofObject ob1, ProofObject ob2, TRS trs, String property) {
    return new ProofObject() {
      public Answer queryAnswer() { return ob1.queryAnswer(); }
      public void justify(OutputModule module) {
        module.print("We consider %a of the ", property);
        module.printTrs(trs);
        ob1.justify(module);
        if (ob2 != null) ob2.justify(module);
      }
    };
  }
  private static ProofObject wrap(ProofObject ob, TRS trs, String property) {
    return wrap(ob, null, trs, property);
  }
}

