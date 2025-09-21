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
import charlie.util.Pair;
import charlie.terms.position.Position;
import charlie.terms.position.FinalPos;
import charlie.terms.Term;
import charlie.terms.FunctionSymbol;
import charlie.substitution.MutableSubstitution;
import charlie.trs.Rule;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionSimplify;

/** This class automates finding a single simplification step that can be applied. */
public final class AutoSimplifier {
  /**
   * This either creates a pre-verified simplify step for some position in the top equation and
   * rule, or null if there is no simplify rule that can be applied.
   */
  public static DeductionSimplify createSingleStep(PartialProof proof) {
    EquationContext ec = proof.getProofState().getTopEquation();
    for (Pair<Term,Position> pair : ec.getLhs().querySubterms()) {
      DeductionSimplify step = findHeadSimplification(pair.fst(), EquationPosition.Side.Left,
                                                      pair.snd(), proof);
      if (step != null) return step;
    }
    for (Pair<Term,Position> pair : ec.getRhs().querySubterms()) {
      DeductionSimplify step = findHeadSimplification(pair.fst(), EquationPosition.Side.Right,
                                                      pair.snd(), proof);
      if (step != null) return step;
    }
    return null;
  }

  /**
   * This function checks if there is any rule that can be used to simplify s at the head, and if
   * so, returns it.  If there is not, then null is returned instead.  Note that this may involve
   * multiple calls to the SMT solver.
   */
  private static DeductionSimplify findHeadSimplification(Term s, EquationPosition.Side side,
                                                          Position pos, PartialProof proof) {
    if (!s.isFunctionalTerm()) return null;
    ProofContext context = proof.getContext();
    FunctionSymbol f = s.queryRoot();
    int n = s.numberArguments();
    int k = context.queryRuleArity(f);
    if (n < k) return null;
    EquationPosition ep;
    if (n > k) ep = new EquationPosition(side, pos.append(new FinalPos(n - k)));
    else ep = new EquationPosition(side, pos);
    MutableSubstitution empty = new MutableSubstitution();
    Optional<OutputModule> m = Optional.empty();
    for (String rulename : context.queryRuleNamesByFunction(s.queryRoot())) {
      DeductionSimplify attempt = DeductionSimplify.createStep(proof, m, rulename, ep, empty);
      if (attempt != null && attempt.verify(m)) return attempt;
    }
    return null;
  }
}

