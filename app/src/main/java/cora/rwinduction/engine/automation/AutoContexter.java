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
import charlie.util.Pair;
import charlie.terms.position.Position;
import charlie.terms.position.ArgumentPos;
import charlie.terms.Term;
import cora.rwinduction.engine.*;

/** This class automates finding the best CONTEXT step that can be applied on the top equation. */
public final class AutoContexter {
  /** 
   * This function edits the two lists, posses and pairs, by adding p into posses and (s|_p,t|_p)
   * into pairs, where p is any of the parallel positions so that s|_p and t|_p are distinct and
   * the terms without the given positions are maximal semi-constructor contexts.
   *
   * That is, we find all positions p, in lexicographical ordering, so that the positions above p
   * refer have the same semi-constructor shape in s and t, so that s|_p != t|_p, and s|_p and t|_p
   * do not themselves have the same semi-constructor shape.
   *
   * We only consider argument contexts, not head contexts.
   */
  public static void storeDifferences(Term s, Term t, ProofContext context, ArrayList<Position>
                                      posses, ArrayList<Pair<Term,Term>> pairs) {
    // If the heads are not the same, we clearly are not part of a context surrounding a difference
    // (as we only consider argument contexts, not head contexts), so return [(ε,(s,t))].
    if (!s.queryHead().equals(t.queryHead()) || s.numberArguments() != t.numberArguments()) {
      posses.add(Position.empty);
      pairs.add(new Pair<Term,Term>(s,t));
      return;
    }
    // similarly, if we're not a semi-constructor context, we must return either [(ε,(s,t))] (if
    // s and t are unequal) or [] (if they are equal)
    if (!s.isFunctionalTerm() || s.numberArguments() >= context.queryRuleArity(s.queryRoot())) {
      if (!s.equals(t)) {
        posses.add(Position.empty);
        pairs.add(new Pair<Term,Term>(s,t));
      }
      return;
    }
    // otherwise, recursively descend into the children and detect differences there
    int n = s.numberArguments();
    int k = posses.size();
    for (int i = 1; i <= n; i++) {
      storeDifferences(s.queryArgument(i), t.queryArgument(i), context, posses, pairs);
      if (posses.size() > k) {
        for (int j = k; j < posses.size(); j++) {
          // update the position to be in the current terms, not the subterms
          posses.set(j, new ArgumentPos(i, posses.get(j)));
        }
        k = posses.size();
      }
    }
  }

  /**
   * This function automatically finds a semi-constructor context for the top equation if this can
   * be done; if not, false is returned.
   * If it is possible, then this context step is added to steps, followed by any disprove,
   * eq-delete and hdelete steps that can be done to either find a contradiction in the proof state,
   * or immediately eliminate a resulting equation.  Hence, any remaining equations resulting from
   * this are not easily removable.
   *
   * All returned steps are immediately executed on the proof.
   */
  public static boolean makeSemiContext(PartialProof proof, ArrayList<DeductionStep> steps) {
    EquationContext ec = proof.getProofState().getTopEquation();

    ArrayList<Position> posses = new ArrayList<Position>();
    ArrayList<Pair<Term,Term>> pairs = new ArrayList<Pair<Term,Term>>();
    storeDifferences(ec.getLhs(), ec.getRhs(), proof.getContext(), posses, pairs);
    if (posses.size() == 0) return false;   // they should be using DELETE instead!
    if (posses.size() == 1 && posses.get(0).isEmpty()) return false;
    // a non-empty context has been found!

    // TODO
    return false;
  }
}

