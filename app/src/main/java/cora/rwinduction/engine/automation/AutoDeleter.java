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
import charlie.terms.position.*;
import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.substitution.Substitution;
import charlie.substitution.MutableSubstitution;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.*;

/**
 * This class automates finding a DELETE, EQ-DELETE, HDELETE or DISPROVE step that can be applied
 * to remove the current top equation (or, in the case of DISPROVE, to end the proof altogether).
 */
public final class AutoDeleter {
  /**
   * An EndingStep contains all the information that should be provided to create one of the steps
   * that immediately removes an equation context, or ends the proof with a successful disprove.
   *
   * The advantage of an EndingStep over an actual DeductionStep is that we can build one based on
   * an equation or equation context, without having the full proof state.
   */
  public interface EndingStep {
    public DeductionStep createStep(PartialProof proof, Optional<OutputModule> module);
    public default boolean requiresCompleteness() { return false; }
  }

  public record DeleteStep() implements EndingStep {
    public DeductionDelete createStep(PartialProof proof, Optional<OutputModule> module) {
      return DeductionDelete.createStep(proof, module);
    }
  }

  public record EqdeleteStep() implements EndingStep {
    public DeductionEqdelete createStep(PartialProof proof, Optional<OutputModule> module) {
      return DeductionEqdelete.createStep(proof, module);
    }
  }

  public record DisproveTheoryStep(Substitution subst) implements EndingStep {
    public DeductionDisproveTheory createStep(PartialProof proof, Optional<OutputModule> module) {
      return DeductionDisproveTheory.createStep(proof, module, subst);
    }
    public boolean requiresCompleteness() { return true; }
  }

  public record DisproveRootStep() implements EndingStep {
    public DeductionDisproveRoot createStep(PartialProof proof, Optional<OutputModule> module) {
      return DeductionDisproveRoot.createStep(proof, module);
    }
    public boolean requiresCompleteness() { return true; }
  }

  /**
   * If the top equation in the given proof can be deleted, this returns the verified DeleteStep to
   * do so and immediately executes it.  If not, null is returned instead.
   */
  public static DeductionDelete tryPureDelete(PartialProof proof) {
    Optional<OutputModule> empty = Optional.empty();
    DeductionDelete ret = DeductionDelete.createStep(proof, empty);
    if (ret == null || !ret.verifyAndExecute(proof, empty)) return null;
    return ret;
  }

  /**
   * This finds an application of hdelete that works, if any is applicable (unless the left- and
   * right-hand side are already equal, in which case null is returned whether or not there is also
   * an applicable hypothesis).  If there is no suitable application of hdelete (or deletion is
   * possible directly), an appropriate message is printed on the given output module.
   */
  public static DeductionStep createHdeleteStep(PartialProof proof,
                                                Optional<OutputModule> module) {
    EquationContext ec = proof.getProofState().getTopEquation();
    EndingStep step = seekHdelete(ec.getLhs(), ec.getRhs(), ec.getConstraint(),
                                  ec.getLeftGreaterTerm(), ec.getRightGreaterTerm(),
                                  proof.getProofState(), module);
    if (step == null) return null;
    return step.createStep(proof, module);
  }

  /**
   * This finds an application of hdelete that works, if any is applicable (unless the left- and
   * right-hand side are already equal, in which case null is returned whether or not there is also
   * an applicable hypothesis).  If there is no suitable application of hdelete, an appropriate
   * message is printed on the given output module.  If deletion is possible directly, then a
   * message is printed AND an EndingStep returned (to create a DeductionDelete instead of
   * DeductionHdelete).
   *
   * Note that we return the information to create a suitable DeductionHdelete (or DeductionDelete)
   * step for any partial proof whose top proof state has (leftbound, left = right | constraint,
   * rightbound) as its top equation context.  The generated step does not need to be verified; if
   * this returns non-null, verification has already been done.
   */
  public static EndingStep seekHdelete(Term left, Term right, Term constraint, 
                                       Optional<Term> leftbound, Optional<Term> rightbound,
                                       ProofState stateWithHypotheses,
                                       Optional<OutputModule> module) {
    if (leftbound.isPresent() && leftbound.get().equals(left) &&
        rightbound.isPresent() && rightbound.get().equals(right)) {
      module.ifPresent(o -> o.println("No HDELETE step can be applied, because the bounding " +
        "terms of the equation context are both equal to the corresponding side of the " +
        "equation.  Hence, there is no way to apply HDELETE that would not lead to an " +
        "unsatisfiable ordering requirement."));
      return null;
    }

    ArrayList<Pair<Position,Pair<Term,Term>>> lst = contextDifferences(left, right);
    if (lst == null) {
      module.ifPresent(o -> o.println("The left- and right-hand side of the equation are the " +
        "same.  I am using DELETE instead."));
      return new DeleteStep();
    }

    for (Pair<Position,Pair<Term,Term>> pair : lst) {
      EndingStep ret = createHdeleteAtPosition(pair.fst(), pair.snd().fst(),
                                               pair.snd().snd(), constraint,
                                               leftbound, rightbound,
                                               stateWithHypotheses);
      if (ret != null) return ret;
    }
    module.ifPresent(o -> o.println("There is no applicable position where we can clearly apply " +
      "HDELETE with any available induction hypothesis."));
    return null;
  }

  /** 
   * This returns null if s and t are the same, and otherwise a list of tuples (p,s|_p,t|_p) where
   * s|_p and t|_p are different.  Specifically, the positions in this list are in the order
   * p_n, p_{n-1}, ..., p_0 where p_0 = ε and each p_{i+1} is one position deeper than p_i, and
   * the contexts s[?]_{p_i} and t[?]_{p_i} are the same.
   */
  private static ArrayList<Pair<Position,Pair<Term,Term>>> contextDifferences(Term s, Term t) {
    ArrayList<Pair<Position,Pair<Term,Term>>> ret = null;
    // If the heads are not the same, we clearly are not part of a context surrounding a difference
    // (as we only consider argument contexts, not head contexts), so return [(ε,(s,t))].
    if (!s.queryHead().equals(t.queryHead()) || s.numberArguments() != t.numberArguments()) {
      ret = new ArrayList<Pair<Position,Pair<Term,Term>>>();
      ret.add(new Pair<Position,Pair<Term,Term>>(Position.empty, new Pair<Term,Term>(s,t)));
      return ret;
    }   
    int n = s.numberArguments();
    // We have f(s1,...,sn) and f(t1,...,tn); find the first argument i where si != ti.
    int i = 1;
    for (; i <= n; i++) {
      ret = contextDifferences(s.queryArgument(i), t.queryArgument(i));
      if (ret != null) break;
    }   
    // They don't differ anywhere? Then the terms are the same, so return null.
    if (ret == null) return ret;
    // If they differ in more than one spot, return [(ε,(s,t))] again.
    for (int j = i+1; j <= n; j++) {
      if (!s.queryArgument(j).equals(t.queryArgument(j))) {
        ret = new ArrayList<Pair<Position,Pair<Term,Term>>>();
        ret.add(new Pair<Position,Pair<Term,Term>>(Position.empty, new Pair<Term,Term>(s,t)));
        return ret;
      }   
    }   
    // If they only differ in one spot, then we are part of a suitable context!  The list is now
    // [(pn,pairn) ,..., (p1,pair1)]; replace it by [(i pn,pairn), ..., (i p1,pair1), (ε,(s,t))].
    for (int j = 0; j < ret.size(); j++) {
      ret.set(j, new Pair<Position,Pair<Term,Term>>(new ArgumentPos(i, ret.get(j).fst()),
                                                    ret.get(j).snd()));
    }   
    ret.add(new Pair<Position,Pair<Term,Term>>(Position.empty, new Pair<Term,Term>(s,t)));
    return ret;
  }

  /**
   * Helper function for seekHdelete: given that the ordering requirement is not a priori a problem,
   * this tries to find out if the given position admits any hdelete steps.
   * The left and right terms are the subterms of the equation at the given position.  For hdelete
   * to succeed, one side of the hypothesis must match the left, and the other the right.
   */
  private static EndingStep createHdeleteAtPosition(Position pos, Term left, Term right,
                                                    Term constraint, Optional<Term> leftbound,
                                                    Optional<Term> rightbound, ProofState state) {
    int posArity = left.queryType().queryArity();
    MutableSubstitution gamma = new MutableSubstitution();
    for (Hypothesis hypo : state.getHypotheses()) {
      Term hypoLhs = hypo.getLhs();
      int hypoArity = hypoLhs.queryType().queryArity();
      if (hypoArity < posArity) continue;
      Position extra = null;
      if (hypoArity > posArity) {
        extra = new FinalPos(hypoArity - posArity);
        left = left.querySubterm(extra);
        right = right.querySubterm(extra);
      }
      for (int i = 0; i < 2; i++) {
        boolean inverse = i == 1;
        if (DeductionHdelete.checkApplicability(leftbound, left, right, rightbound, constraint,
                                                hypo, inverse)) {
          EquationPosition ep = new EquationPosition(EquationPosition.Side.Left,
                                                     extra == null ? pos : pos.append(extra));
          return new EndingStep() {
            public DeductionHdelete createStep(PartialProof proof, Optional<OutputModule> module) {
              return DeductionHdelete.createStep(proof, module, hypo, inverse, ep, gamma);
            }
          };
        }
      }
    }

    // I went through all the hypotheses and still did not return! ==> There are no good ones.
    return null;
  }

  /** 
   * This function should only be called with equations left = right | constraint where left and
   * right are both fully calculated first-order theory terms (so, base-type variables or values),
   * and if the equation is part of a complete equation context.  If this is not the case,
   * incorrect results may ensue, or even exceptions being thrown.
   *
   * If constraint ∧ left != right is satisfiable, then this equation is disprovable; hence, a
   * disprove step is returned.
   *
   * If constraint ∧ left != right is NOT satisfiable, then constraint ⇒ left = right; hence, an
   * eq-delete step is returned.
   *
   * Finally, if we cannot prove or disprove satisfiability, null is returned.
   */
  static EndingStep seekFODisproveOrEqdelete(Term left, Term right, Term constraint) {
    Term c = TheoryFactory.createConjunction(constraint,
      TheoryFactory.notSymbol.apply(TheoryFactory.createEquality(left, right)));
    switch (TermAnalyser.satisfy(c, Settings.smtSolver)) {
      case TermAnalyser.Result.YES(Substitution subst):
        return new DisproveTheoryStep(subst);
      case TermAnalyser.Result.NO():
        return new EqdeleteStep();
      case TermAnalyser.Result.MAYBE(String reason):
        return null;
    }
  }
}

