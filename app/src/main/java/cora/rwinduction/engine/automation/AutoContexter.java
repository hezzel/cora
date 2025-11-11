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
import charlie.terms.position.ArgumentPos;
import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.substitution.Substitution;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionContext;

/** This class automates finding the best CONTEXT step that can be applied on the top equation. */
public final class AutoContexter {
  /**
   * If it is possible, then this context step is added to steps, followed by any disprove,
   * eq-delete and hdelete steps that can be done to either find a contradiction in the proof state,
   * or immediately eliminate a resulting equation.  Hence, any remaining equations resulting from
   * this are not easily removable.
   *
   * All returned steps are immediately executed on the proof.
   */
/*
  public static boolean makeSemiContext(PartialProof proof, ArrayList<DeductionStep> steps) {
    // find what we can do with each position
    ArrayList<Pair<Position,Substitution>> disprovable =
      new ArrayList<Pair<Position,Substitution>>();
    ArrayList<Pair<Position,Pair<Hypothesis,Boolean>>> hdeletable =
      new ArrayList<Pair<Position,Pair<Hypothesis,Boolean>>>();
    ArrayList<Position> eqdeletable, tricky, rest;
    eqdeletable = new ArrayList<Position>();
    tricky = new ArrayList<Position>();
    rest = new ArrayList<Position>();
    boolean complete = !proof.getProofState().getIncompleteEquations().contains(ec.getIndex());
    categorise(posses, pairs, ec.getConstraint(), complete, proof,
               ec.getLeftGreaterTerm(), ec.getRightGreaterTerm(),
               disprovable, eqdeletable, hdeletable, tricky, rest);

    // make the context step
    Optional<OutputModule> eps = Optional.empty();
    ArrayList<Position> orderedPosses = new ArrayList<Position>();
    for (int i = 0; i < disprovable.size(); i++) orderedPosses.add(disprovable.get(i).fst());
    for (int i = 0; i < eqdeletable.size(); i++) orderedPosses.add(eqdeletable.get(i));
    for (int i = 0; i < hdeletable.size(); i++) orderedPosses.add(hdeletable.get(i).fst());
    for (int i = 0; i < tricky.size(); i++) orderedPosses.add(tricky.get(i));
    for (int i = 0; i < rest.size(); i++) orderedPosses.add(rest.get(i));
    DeductionStep step = DeductionContext.createStep(proof, eps, orderedPosses);
    if (step == null) return false;
    if (!step.execute(proof, eps)) return false;
    steps.add(step);

    // make the other steps
    for (int i = 0; i < disprovable.size(); i++) {
      if (disprovable.get(i).snd() == null) step = DeductionDisproveRoot.createStep(proof, eps);
      else step = DeductionDisproveTheory.createStep(proof, eps, disprovable.get(i).snd());
      if (step == null || !step.execute(proof, eps)) return false;
      steps.add(step);
    }
    for (int i = 0; i < eqdeletable.size(); i++) {
      step = DeductionEqdelete.createStep(proof, eps);
      if (step == null || !step.execute(proof, eps)) return false;
      steps.add(step);
    }
    for (int i = 0; i < hdeletable.size(); i++) {
      step = DeductionHdelete.createStep(proof, eps, hdeletable.get(i).snd().fst(), hdeletable.get(i).snd().snd());
      if (step == null || !step.execute(proof, eps)) return false;
      steps.add(step);
    }

    return true;
  }
*/

  /**
   * This goes over all elements of posses/pairs into storage, and stores them in one of the five
   * categories.
   *
   * If disprovable is non-empty and the first element is a theory pair, then the corresponding
   * substitution is returned.  Otherwise, null is returned.
   */
/*
  private static void categorise(ArrayList<Position> posses, ArrayList<Pair<Term,Term>> pairs,
                                 Term constraint, boolean complete, PartialProof proof,
                                 Optional<Term> leftbound, Optional<Term> rightbound,
                                 ArrayList<Pair<Position,Substitution>> disprovable,
                                 ArrayList<Position> eqdeletable,
                                 ArrayList<Pair<Position,Pair<Hypothesis,Boolean>>> hdeletable,
                                 ArrayList<Position> tricky,
                                 ArrayList<Position> rest) {
    for (int i = 0; i < posses.size(); i++) {
      Position p = posses.get(i);
      Term left = pairs.get(i).fst();
      Term right = pairs.get(i).snd();

      // for first-order theory terms, we can handle several cases at once
      if (left.isTheoryTerm() && right.isTheoryTerm() && left.isFirstOrder() &&
          right.isFirstOrder()) {
        checkFOTheoryDisprove(p, left, right, constraint, complete, disprovable, eqdeletable, tricky);
        return;
      }
      // ohterwise, we try disprove, eqdelete and hdelete separately
      if (tryDisprove(left, right, constraint, p, complete, proof.getContext(), disprovable,
                      tricky)) return;
      if (tryComplexEqdelete(left, right, constraint, p, eqdeletable)) return;
      Pair<Hypothesis,Boolean> pair = AutoDeleter.tryHdeleteAtTop(proof.getProofState(), left,
                                                     right, constraint, leftbound, rightbound);
      if (pair != null) {
        hdeletable.add(new Pair<Position,Pair<Hypothesis,Boolean>>(p, pair));
        return;
      }
      if (left.isTheoryTerm() && right.isTheoryTerm()) tricky.add(p);
      else rest.add(p);
    }
  }
*/
}

