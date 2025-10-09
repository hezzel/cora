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
import java.util.Collections;
import java.util.Comparator;
import java.util.Optional;
import charlie.util.Pair;
import charlie.terms.position.Position;
import charlie.terms.position.FinalPos;
import charlie.terms.Term;
import charlie.terms.FunctionSymbol;
import charlie.substitution.MutableSubstitution;
import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.EquationPosition.Side;
import cora.rwinduction.engine.deduction.DeductionHypothesis;

/**
 * This class automates finding a HYPOTHESIS step.  This is somewhat dubious, since when there are
 * multiple choices it is not necessarily obvious which one should be applied, and order matters.
 * So, if there are multiple options on the same position, we won't do it.  Otherwise, we'll make
 * an educated guess!
 */
public final class AutoHypothesis {
  /**
   * This tries to find an application of hypothesis that works, provided one can be found where
   * there isn't another hypothesis at the same position, and which is not inferior to other
   * possible induction hypothesis steps.
   *
   * If we cannot determine a good induction hypothesis, or cannot choose one between multiple
   * reasonable options, then an appropriate message is put on the output module and null is
   * returned.  Otherwise, the step is returned.
   */
  public static DeductionHypothesis createHypothesisStep(PartialProof proof,
                                                         OutputModule module) {
    EquationContext ec = proof.getProofState().getTopEquation();
    
    // determine which side to try first
    Term a, b;
    Side aside, bside;
    int ascore, bscore;
    TRS trs = proof.getContext().getTRS();
    if (!ec.getLeftGreaterTerm().isPresent()) ascore = 100;
    else ascore = sideScore(trs, ec.getLeftGreaterTerm().get(), ec.getLhs());
    if (!ec.getRightGreaterTerm().isPresent()) bscore = 100;
    else bscore = sideScore(trs, ec.getRightGreaterTerm().get(), ec.getRhs());
    if (ascore >= bscore) {aside = Side.Left; bside = Side.Right; a = ec.getLhs(); b = ec.getRhs();}
    else { aside = Side.Right; bside = Side.Left; a = ec.getRhs(); b = ec.getLhs(); }

    // go over all positions in the priority side, and find a position where only one step can be
    // applied, if possible
    ArrayList<DeductionHypothesis> options = new ArrayList<DeductionHypothesis>();
    int count = 0;
    for (Pair<Term,Position> pair : a.querySubterms()) {
      tryStep(pair.fst(), aside, pair.snd(), proof, options);
      if (options.size() == count + 1) return options.get(count);
      count = options.size();
    }

    // if we haven't found any good position in the priority side, or we have found multiple and the
    // non-priority side is just as good, try that side, too
    if (options.size() == 0 || ascore == bscore) {
      for (Pair<Term,Position> pair : b.querySubterms()) {
        tryStep(pair.fst(), bside, pair.snd(), proof, options);
        if (options.size() == count + 1) return options.get(count);
        count = options.size();
      }
    }

    if (options.size() == 0) {
      module.println("I cannot find a place where an induction hypothesis can clearly be applied.");
    }
    else {
      module.println("There are multiple possible induction hypothesis steps, and it is not " +
        "obvious which to choose from the following:");
      module.startTable();
      for (DeductionHypothesis step : options) {
        module.nextColumn("*");
        module.println(step.commandDescription());
      }
      module.endTable();
    }
    return null;
  }

  /**
   * This returns the side that is likely to yield the least harmful ordering requirements.  If
   * there is no clear difference, Left is returned.
   */
  static Side chooseBestSide(TRS trs, EquationContext ec) {
    // constraints • t are always satisfied, so if we can create those, do!
    if (!ec.getLeftGreaterTerm().isPresent()) return Side.Left;
    if (!ec.getRightGreaterTerm().isPresent()) return Side.Right;
    // otherwise, pick the side with the highest score
    if (sideScore(trs, ec.getLeftGreaterTerm().get(), ec.getLhs()) >=
        sideScore(trs, ec.getRightGreaterTerm().get(), ec.getRhs())) return Side.Left;
    else return Side.Right;
  }
  
  /**
   * This function assigns a score to a side of an equation (s', s = t | φ, t') if either
   * s' = bounder and s = main, or t' = bounder and t = main.  If one side scores higher than the
   * other, than that side is likely to have easier ordering requirements.
   */
  private static int sideScore(TRS trs, Term bounder, Term main) {
    return 2 * leftOfOrderingRequirementScore(trs, bounder) + (bounder.equals(main) ? 0 : 1);
  }

  /**
   * This function assigns to a term a score in the range 0-3 for how easy it is to handle
   * requirements of the form term ≻ s | φ.  A greater score means that it is typically easier.
   */
  private static int leftOfOrderingRequirementScore(TRS trs, Term term) {
    if (!term.isFunctionalTerm()) return 0;
    if (term.queryRoot().toCalculationSymbol() != null) return 1;
    if (!trs.isDefined(term.queryRoot())) return 2;
    return 3;
  }

  /**
   * This tries to create any possible Hypothesis step at the equation position side.pos*n for some
   * n ≥ 0, given that the subterm at equation position side.pos is s.  Any step that is found (and
   * verified) is added to the given list.
   */
  private static DeductionHypothesis tryStep(Term s, Side side, Position pos, PartialProof proof,
                                             ArrayList<DeductionHypothesis> ret) {
    int sar = s.queryType().queryArity();
    FunctionSymbol f = s.isFunctionalTerm() ? s.queryRoot() : null;
    for (Hypothesis hypo : proof.getProofState().getHypotheses()) {
      int har = hypo.getLhs().queryType().queryArity();
      if (har < sar) continue;
      if (har != sar) pos = pos.append(new FinalPos(har - sar));
      if (f == null || !hypo.getLhs().isFunctionalTerm() ||
          f.equals(hypo.getLhs().queryRoot())) {
        DeductionHypothesis step = DeductionHypothesis.createStep(proof, Optional.empty(), hypo,
                 false, new EquationPosition(side, pos), new MutableSubstitution());
        if (step != null && step.verify(Optional.empty())) ret.add(step);
      }
      if (f == null || !hypo.getRhs().isFunctionalTerm() ||
          f.equals(hypo.getRhs().queryRoot())) {
        DeductionHypothesis step = DeductionHypothesis.createStep(proof, Optional.empty(), hypo,
                  true, new EquationPosition(side, pos), new MutableSubstitution());
        if (step != null && step.verify(Optional.empty())) ret.add(step);
      }
    }
    return null;
  }
}

