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

package cora.termination.transformation;

import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.*;
import charlie.trs.*;

import java.util.ArrayList;
import java.util.TreeSet;

/**
 * The CallByValueModifier class modifies an existing TRS by changing all rules to store all
 * variables of a theory sort into the constraint (since, in call-by-value evaluation, these can
 * be assumed to be instantiated only with values).
 */
public class CallByValueModifier {
  private TRS _trs;
  private TreeSet<String> _badTheorySorts;

  /** Returns whether or not the current technique is applicable to the given TRS. */
  public static boolean isApplicable(TRS trs) {
    if (!trs.verifyProperties(TrsProperties.Level.META, TrsProperties.Constrained.YES,  
                              TrsProperties.TypeLevel.SIMPLE, TrsProperties.Lhs.NONPATTERN,
                              TrsProperties.Root.ANY, TrsProperties.FreshRight.ANY)) {
      return false;
    }
    // we're not applicable if term values of theory sort cannot be assumed to be theory values
    for (FunctionSymbol f : trs.queryAlphabet().getSymbols()) {
      if (f.isTheorySymbol()) continue;
      if (trs.isDefined(f)) continue;
      Type type = f.queryType().queryOutputType();
      if (type.isTheoryType() && type.isBaseType()) return false;
    }
    return true;
  }

  /**
   * Main function: modifies the given TRS.
   * NOTE: this should only be called if isApplicable(trs) returns true, otherwise soundness is not
   * guaranteed.
   */
  public static TRS modify(TRS trs) {
    ArrayList<Rule> newrules = new ArrayList<Rule>();
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rho = trs.queryRule(i);
      Term left = rho.queryLeftSide();
      Term right = rho.queryRightSide();
      Term constraint = rho.queryConstraint();
      Environment<Variable> cvars = constraint.vars();
      Term newconstraint = constraint;
      for (Variable x : left.vars()) {
        if (!x.queryType().isBaseType() || !x.queryType().isTheoryType()) continue;
        if (cvars.contains(x)) continue;
        Term eq = TheoryFactory.createEquality(x, x);
        newconstraint = TheoryFactory.createConjunction(newconstraint, eq);
      }
      newrules.add(TrsFactory.createRule(left, right, newconstraint));
    }
    return trs.createDerivative(newrules);
  }

}
