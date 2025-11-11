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
import charlie.terms.Term;
import charlie.substitution.Substitution;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionContext;
import cora.rwinduction.engine.deduction.DeductionDisproveRoot;
import cora.rwinduction.engine.deduction.DeductionEqdelete;

/**
 * This class organises the automatic reasoning abilities of the rewriting inducter.
 */
public final class AutomaticProver {
  /**
   * This function does obvious steps on the top goal: simplifying, calculating, and various ways
   * of deleting.
   */
  public static ArrayList<DeductionStep> handleBasics(PartialProof proof) {
    // simplify and calculate as far as we can
    ArrayList<DeductionStep> ret = AutoSimplifier.simplifyFully(proof);
    EquationContext ec = proof.getProofState().getTopEquation();
    // see if we can just delete the result!
    DeductionStep dd = AutoDeleter.tryPureDelete(proof);
    if (dd != null) { ret.add(dd); return ret; }
    // get the basic information for a context step
    ArrayList<Position> posses = new ArrayList<Position>();
    ArrayList<Pair<Term,Term>> pairs = new ArrayList<Pair<Term,Term>>();
    DeductionContext.storeDifferences(ec.getLhs(), ec.getRhs(), proof.getContext(), posses, pairs);
    // check all relevant subterms (or the top equation itself, if posses = [ε]) if they can be
    // eq-deleted, hdeleted or disproved (deletion itself is not possible, or it could have been
    // done already before splitting up the context)
    boolean incomplete = proof.getProofState().getIncompleteEquations().contains(ec.getIndex());
    ArrayList<AutoDeleter.EndingStep> steps = new ArrayList<AutoDeleter.EndingStep>();
    posses = categoriseAndReorder(pairs, posses, ec.getLeftGreaterTerm(), ec.getRightGreaterTerm(),
                 ec.getConstraint(), proof.getProofState(), proof.getContext(), incomplete, steps);
    // create the posses step (or fail to do so if we only have the position ε)
    Optional<OutputModule> empty = Optional.empty();
    DeductionContext dc = DeductionContext.createStep(proof, Optional.empty(), posses);
    if (dc != null && dc.verifyAndExecute(proof, empty)) ret.add(dc);
    // do all the steps!
    for (AutoDeleter.EndingStep step : steps) {
      DeductionStep s = step.createStep(proof, empty);
      if (s == null) {
        throw new RuntimeException("handleBasics created a step that cannot be created!");
      }
      if (!s.execute(proof, empty)) {
        throw new RuntimeException("handleBasics created a step " + s.commandDescription() +
          " that cannot be executed!");
      }
      ret.add(s);
    }

    return ret;
  }

  /**
   * Helper function for handleBasics: given that pairs and posses have the same size, this function
   * goes over all pairs, categorises them, and returns a reordered copy of posses, as follows:
   * - For all pairs of terms that can be deleted or lead to a disprove, they are moved to the
   *   start of the returned position list, and steps contains the steps to delete them.
   * - The remaining positions are listed after the deletable ones in the returned list, with no
   *   corresponding step in steps.  There is some attempt to put the more annoying positions first,
   *   so a human user can see that they have run into trouble as quickly as possible.
   */
  private static ArrayList<Position> categoriseAndReorder(ArrayList<Pair<Term,Term>> pairs,
        ArrayList<Position> posses, Optional<Term> leftbound, Optional<Term> rightbound,
        Term constraint, ProofState state, ProofContext context, boolean incomplete,
        ArrayList<AutoDeleter.EndingStep> steps) {
    ArrayList<Position> ret = new ArrayList<Position>();
    ArrayList<Position> tricky = new ArrayList<Position>();
    ArrayList<Position> rest = new ArrayList<Position>();
    for (int i = 0; i < posses.size(); i++) {
      Position p = posses.get(i);
      Term left = pairs.get(i).fst();
      Term right = pairs.get(i).snd();
      AutoDeleter.EndingStep step = categorise(left, right, constraint, leftbound, rightbound,
                                               state, context, incomplete);
      if (step == null) {
        if (left.isTheoryTerm() && right.isTheoryTerm()) tricky.add(p);
        else rest.add(p);
      }
      else if (step.requiresCompleteness() && incomplete) tricky.add(p);
      else {
        ret.add(p);
        steps.add(step);
      }
    }
    for (Position pos : tricky) ret.add(pos);
    for (Position pos : rest) ret.add(pos);
    return ret;
  }

  /**
   * Helper function for handleBasics: this returns for a given equation context
   * (leftbound, left = right | constraint, rightbound) that is already known to be fully
   * simplified/calculated and is not deletable, a potential "ending step" that can be done on it.
   * If none can be found, null is returned instead.
   *
   * If incomplete is set to true, then it is still possible for disprove steps to be returned, but
   * we will not go to great effort to find them (i.e., there will be no additional SMT checks to
   * find a disprove step if it cannot be executed anyway).
   *
   * Default rather than private only for the sake of unit testing.
   */
  static AutoDeleter.EndingStep categorise(Term left, Term right, Term constraint,
                                           Optional<Term> leftbound, Optional<Term> rightbound,
                                           ProofState state, ProofContext context,
                                           boolean incomplete) {
    // if it's pure theory, and first-order to boot, we should be able to manage it with the
    // SMT-solver
    if (left.isTheoryTerm() && right.isTheoryTerm() &&
        left.isFirstOrder() && right.isFirstOrder()) {
      return AutoDeleter.seekFODisproveOrEqdelete(left, right, constraint);
    }
    // if we can find an eq-delete (which cannot be at the top), do that
    if (DeductionEqdelete.checkApplicability(left, right, constraint)) {
      return new AutoDeleter.EqdeleteStep();
    }
    // if we can find an h-delete, do that
    AutoDeleter.EndingStep step = AutoDeleter.seekHdelete(left, right, constraint, leftbound,
                                                          rightbound, state, Optional.empty());
    if (step != null) return step;
    // if we can find a _cheap_ disprove, return that
    if (DeductionDisproveRoot.checkDifferentSemiconstructors(left, right, context) != null) {
      return new AutoDeleter.EndingStep() {
        public DeductionDisproveRoot createStep(PartialProof proof, Optional<OutputModule> module) {
          return DeductionDisproveRoot.createStep(proof, module);
        }
        public boolean requiresCompleteness() { return true; }
      };
    }
    // if we are complete, also try finding an expensive disprove step
    if (incomplete) return null;
    Substitution subst = AutoDisprover.findContradictingTheorySubstitution(left, right, constraint,
                                                                           Optional.empty(), null);
    if (subst != null) return new AutoDeleter.DisproveTheoryStep(subst);
    return null;
  }
}

