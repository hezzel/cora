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
import java.util.LinkedList;
import java.util.Optional;
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
    Function<Integer,EquationPosition> positionMaker = i ->
      i > 0 ? new EquationPosition(side, pos.append(new FinalPos(i)))
            : new EquationPosition(side, pos);
    return findHeadSimplification(sub, positionMaker, proof);
  }

  /**
   * This function checks if there is any rule that can be used to simplify s at the head, and if
   * so, returns it.  If there is not, then null is returned instead.  Note that this may involve
   * multiple calls to the SMT solver.
   *
   * The posMaker argument should return, given a chopcount c, p*i, where p is the position in the
   * top equation where s can be found.
   */
  private static DeductionSimplify findHeadSimplification(Term s, Function<Integer,EquationPosition>
                                                          posMaker, PartialProof proof) {
    if (!s.isFunctionalTerm()) return null;
    ProofContext context = proof.getContext();
    FunctionSymbol f = s.queryRoot();
    int n = s.numberArguments();
    int k = context.queryRuleArity(f);
    if (n < k) return null;
    EquationPosition ep = posMaker.apply(n - k);
    MutableSubstitution empty = new MutableSubstitution();
    Optional<OutputModule> m = Optional.empty();
    for (String rulename : context.queryRuleNamesByFunction(s.queryRoot())) {
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
    /*
    while (true) {
      // first simplify the arguments and replace s accordingly
      int count = steps.size();
      ArrayList<Term> args = new ArrayList<Term>(s.numberArguments());
      for (int i = 1; i <= s.numberArguments(); i++) {
        pos.add(i);
        args.add(simplifyFully(proof, s.queryArgument(i), side, pos, steps));
        pos.removeLast();
      }
      if (steps.size() != count) s = s.queryHead().apply(args);
  
      // try reducing at the head!
      DeductionSimplify step = findHeadSimplification(s, i -> makePos(side, pos, i), proof);
      if (step == null || !step.execute(Optional.empty(proof))) return s;
      s = step.queryReplacementSubterm();
    }
    */
    return null;
  }

  private static EquationPosition makePos(EquationPosition.Side side, LinkedList<Integer> main,
                                          int chop) {
    Position p = new FinalPos(chop);
    while (!main.isEmpty()) p = new ArgumentPos(main.removeLast(), p);
    return new EquationPosition(side, p);
  }
}

