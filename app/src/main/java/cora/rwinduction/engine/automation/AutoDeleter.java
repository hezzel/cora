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
import charlie.substitution.MutableSubstitution;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionHdelete;

/**
 * This class automates finding a DELETE, EQ-DELETE or HDELETE step that can be applied to remove
 * the current top equation.
 */
public final class AutoDeleter {
  /**
   * This finds an application of hdelete that works, if any is applicable (unless the left- and
   * right-hand side are already equal, in which case null is returned whether or not there is also
   * an applicable hypothesis).  If there is no suitable application of hdelete (or deletion is
   * possible directly), an appropriate message is printed on the given output module.
   */
  public static DeductionHdelete createHdeleteStep(PartialProof proof,
                                                   Optional<OutputModule> module) {
    EquationContext ec = proof.getProofState().getTopEquation();
    if (ec.getLeftGreaterTerm().isPresent() && ec.getLeftGreaterTerm().get().equals(ec.getLhs()) &&
        ec.getRightGreaterTerm().isPresent() && ec.getRightGreaterTerm().get().equals(ec.getRhs()))
    {
      module.ifPresent(o -> o.println("No HDELETE step can be applied, because the bounding " +
        "terms of the equation context are both equal to the corresponding side of the " +
        "equation.  Hence, there is no way to apply HDELETE that would not lead to an " +
        "unsatisfiable ordering requirement."));
      return null;
    }

    ArrayList<Pair<Position,Pair<Term,Term>>> lst = contextDifferences(ec.getLhs(), ec.getRhs());
    if (lst == null) {
      module.ifPresent(o -> o.println("The left- and right-hand side of the equation are the " +
        "same.  Use DELETE instead!"));
      return null;
    }

    for (Pair<Position,Pair<Term,Term>> pair : contextDifferences(ec.getLhs(), ec.getRhs())) {
      DeductionHdelete ret = createHdeleteAtPosition(proof, pair.fst(),
                                                     pair.snd().fst(), pair.snd().snd());
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
   * Helper function for createHdeleteStep: given that the ordering requirement is not a priori a
   * problem, this tries to find out if the given position admits any hdelete steps.
   * The left and right terms are the subterms of the equation at the given position.  For hdelete
   * to succeed, one side of the hypothesis must match the left, and the other the right.
   */
  private static DeductionHdelete createHdeleteAtPosition(PartialProof proof, Position pos,
                                                          Term left, Term right) {
    int posArity = left.queryType().queryArity();
    Optional<OutputModule> empty = Optional.empty();
    MutableSubstitution gamma = new MutableSubstitution();
    for (Hypothesis hypo : proof.getProofState().getHypotheses()) {
      Term hypoLhs = hypo.getLhs();
      Term hypoRhs = hypo.getRhs();
      int hypoArity = hypoLhs.queryType().queryArity();
      if (hypoArity < posArity) continue;
      EquationPosition p = null;
      // try applying the hypothesis from left to right
      if ( (!hypoLhs.isFunctionalTerm() || hypoLhs.queryRoot().equals(left.queryHead())) &&
           (!hypoRhs.isFunctionalTerm() || hypoRhs.queryRoot().equals(right.queryHead())) ) {
        p = new EquationPosition(EquationPosition.Side.Left,
              posArity == hypoArity ? pos : pos.append(new FinalPos(hypoArity - posArity)));
        DeductionHdelete ret = DeductionHdelete.createStep(proof, empty, hypo, false, p, gamma);
        if (ret != null && ret.verify(empty)) return ret;
      }
      // try applying the hypothesis from right to left
      if ( (!hypoLhs.isFunctionalTerm() || hypoLhs.queryRoot().equals(right.queryHead())) &&
           (!hypoRhs.isFunctionalTerm() || hypoRhs.queryRoot().equals(left.queryHead())) ) {
        if (p == null) p = new EquationPosition(EquationPosition.Side.Left,
              posArity == hypoArity ? pos : pos.append(new FinalPos(posArity - hypoArity)));
        DeductionHdelete ret = DeductionHdelete.createStep(proof, empty, hypo, true, p, gamma);
        if (ret != null && ret.verify(empty)) return ret;
      }
    }
    // I went through all the hypotheses and still did not return! ==> There are no good ones.
    return null;
  }
}

