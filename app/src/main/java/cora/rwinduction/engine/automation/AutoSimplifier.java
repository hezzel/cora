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

import java.util.*;
import java.util.function.Function;
import charlie.util.Pair;
import charlie.terms.position.*;
import charlie.terms.Term;
import charlie.terms.FunctionSymbol;
import charlie.substitution.MutableSubstitution;
import charlie.trs.Rule;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;
import cora.rwinduction.engine.deduction.DeductionSimplify;
import cora.rwinduction.engine.deduction.DeductionCalc;

/** This class automates finding a single simplification step that can be applied. */
public final class AutoSimplifier {
  /**
   * This either creates a pre-verified simplify step for some position in the top equation and
   * rule, or null if there is no simplify rule that can be applied.
   */
  public static DeductionSimplify createSingleStep(PartialProof proof) {
    EquationContext ec = proof.getProofState().getTopEquation();
    for (Pair<Term,Position> pair : ec.getLhs().querySubterms()) {
      DeductionSimplify step =
        createSingleStepAtPosition(proof, EquationPosition.Side.Left, pair.snd(), pair.fst());
      if (step != null) return step;
    }
    for (Pair<Term,Position> pair : ec.getRhs().querySubterms()) {
      DeductionSimplify step =
        createSingleStepAtPosition(proof, EquationPosition.Side.Right, pair.snd(), pair.fst());
      if (step != null) return step;
    }
    return null;
  }

  /**
   * Helper function for createSingleStep: given that the top equation has sub at position side.pos,
   * this tries to find a single step to apply on sub.  If successful, the step is returned; if not,
   * null is returned instead.
   */
  private static DeductionSimplify createSingleStepAtPosition(PartialProof proof,
                                                              EquationPosition.Side side,
                                                              Position pos, Term sub) {
    if (!sub.isFunctionalTerm()) return null;
    Function<Integer,EquationPosition> positionMaker = i ->
      i > 0 ? new EquationPosition(side, pos.append(new FinalPos(i)))
            : new EquationPosition(side, pos);
    return findHeadSimplification(proof, sub.queryRoot(), sub.numberArguments(), positionMaker);
  }

  /**
   * Given that the top equation, at position side.pos, has a subterm f(s1...sn) with n =
   * numberArguments, this function tries to find a DeductionSimplify step that can be applied at
   * that position or at its head.  Note that this may involve multiple calls to the SMT-solver.
   *
   * If such a step can be found it is returned; if not, null is returned.
   *
   * The posMaker argument should return, given a chopcount c, p*i, where p is the position in the
   * top equation where s can be found.
   */
  private static DeductionSimplify findHeadSimplification(PartialProof proof, FunctionSymbol f,
                              int numberArguments, Function<Integer,EquationPosition> posMaker) {
    int k = proof.getContext().queryRuleArity(f);
    if (numberArguments < k) return null;
    EquationPosition ep = posMaker.apply(numberArguments - k);
    MutableSubstitution empty = new MutableSubstitution();
    Optional<OutputModule> m = Optional.empty();
    Set<String> names = proof.getContext().queryRuleNamesByFunction(f);
    if (names == null) return null;
    for (String rulename : names) {
      DeductionSimplify attempt = DeductionSimplify.createStep(proof, m, rulename, ep, empty);
      if (attempt != null && attempt.verify(m)) return attempt;
    }
    return null;
  }

  /**
   * This function takes the current proof states, and applies Simplify and Calc steps until none
   * apply any longer.  The list of all steps done is returned.
   */
  public static ArrayList<DeductionStep> simplifyFully(PartialProof proof) {
    EquationContext ec = proof.getProofState().getTopEquation();
    ArrayList<DeductionStep> ret = new ArrayList<DeductionStep>();
    simplifyFully(proof, ec.getLhs(), EquationPosition.Side.Left, new LinkedList<Integer>(), ret);
    simplifyFully(proof, ec.getRhs(), EquationPosition.Side.Right, new LinkedList<Integer>(), ret);
    return ret;
  }

  /**
   * Helper function for simplifyFully.  Given that the [side] side of the equation, at position
   * [pos], is s, and that all subterms to the left of this position have already been normalised,
   * this adds the steps to [steps] to also normalise s, and applies these steps to the proof.  It
   * also returns the updated term s.
   * Note that this may involve many calls to the SMT solver.
   */
  private static Term simplifyFully(PartialProof proof, Term s, EquationPosition.Side side,
                                    LinkedList<Integer> pos, ArrayList<DeductionStep> steps) {
    while (true) {
      // first simplify the arguments and replace s accordingly
      int count = steps.size();
      ArrayList<Term> args = new ArrayList<Term>(s.numberArguments());
      for (int i = 1; i <= s.numberArguments(); i++) {
        pos.add(i);
        args.add(simplifyFully(proof, s.queryArgument(i), side, pos, steps));
        pos.removeLast();
      }
      if (!s.isFunctionalTerm()) {
        if (steps.size() == count) return s;
        return s.queryHead().apply(args);
      }
      DeductionStep step;
      if (s.queryRoot().toCalculationSymbol() != null && s.queryType().isBaseType()) {
        step = findCalculation(proof, side, pos, args);
      }
      else step = findHeadSimplification(proof, s.queryRoot(), s.numberArguments(),
                                        i -> makePos(side, pos, i));
      if (step == null || !step.execute(proof, Optional.empty())) return s.queryHead().apply(args);
      steps.add(step);
      System.out.println("Executed " + step + "; now equation = " + proof.getProofState().getTopEquation());
      s = proof.getProofState().getTopEquation().getEquation().querySubterm(makePos(side, pos, 0));
    }
  }

  /**
   * Helper function for simplifyFully: if a calculation symbol applied to (fully simplified) args
   * can be calculated at the root, then the corresponding reduction step is returned; otherwise
   * null.
   */
  private static DeductionCalc findCalculation(PartialProof proof, EquationPosition.Side side,
                                               LinkedList<Integer> pos, ArrayList<Term> args) {
    for (Term term : args) {
      if (!term.isValue() && !term.isVariable()) return null;
    }
    Optional<OutputModule> empty = Optional.empty();
    DeductionCalc ret = DeductionCalc.createStep(proof, empty, List.of(makePos(side, pos, 0)));
    if (ret == null || !ret.verify(empty)) return null;
    return ret;
  }

  private static EquationPosition makePos(EquationPosition.Side side, LinkedList<Integer> main,
                                          int chop) {
    Position p = new FinalPos(chop);
    Iterator<Integer> iterator = main.descendingIterator();
    while (iterator.hasNext()) p = new ArgumentPos(iterator.next(), p);
    return new EquationPosition(side, p);
  }
}

