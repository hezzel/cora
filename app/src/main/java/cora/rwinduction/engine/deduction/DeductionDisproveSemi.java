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

package cora.rwinduction.engine.deduction;

import java.util.Optional;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This deduction step handles the "disprove" case where both sides can be instantiated to
 * distinct semi-constructor terms.
 */
public final class DeductionDisproveSemi extends DeductionStep {
  private FunctionSymbol _left;
  private FunctionSymbol _right;

  private DeductionDisproveSemi(ProofState state, ProofContext context,
                                FunctionSymbol left, FunctionSymbol right) {
    super(state, context);
    _left = left;
    _right = right;
  }

  public static DeductionDisproveSemi createStep(PartialProof proof, Optional<OutputModule> m) {
    ProofContext context = proof.getContext();
    Equation equation = getTopEquation(proof.getProofState(), m);
    if (equation == null) return null;
    Term left = equation.getLhs();
    Term right = equation.getRhs();
    Pair<FunctionSymbol,FunctionSymbol> pair = checkDifferentSemiconstructors(left, right, context);
    if (pair == null) {
      m.ifPresent(o -> o.println("There is no substitution over the known alphabet that would " +
        "instantiate the left- and right-hand to different semi-constructor terms."));
      return null;
    }
    return new DeductionDisproveSemi(proof.getProofState(), context, pair.fst(), pair.snd());
  }

  /**
   * If the top equation in the current proof state has a left-hand side and right-hand side that
   * can be instantiated to semi-constructor terms with different function symbols at the roots,
   * then this returns the pair of symbols that we can have at the root.
   * Otherwise, it returns null.
   */
  public static Pair<FunctionSymbol,FunctionSymbol> checkDifferentSemiconstructors(Term left,
                                                            Term right, ProofContext context) {
    if (left.queryHead().equals(right.queryHead())) return null;
    FunctionSymbol f = null, g = null;
    if (left.isFunctionalTerm()) {
      f = left.queryRoot();
      if (left.numberArguments() >= context.queryRuleArity(f)) return null;
    }
    if (right.isFunctionalTerm()) {
      g = right.queryRoot();
      if (right.numberArguments() >= context.queryRuleArity(g)) return null;
    }
    if (f == null) {
      f = findSemiConstructor(context, left.queryHead().queryType(), left.numberArguments(), g);
    }
    if (g == null) {
      g = findSemiConstructor(context, right.queryHead().queryType(), right.numberArguments(), f);
    }
    if (f != null && g != null) return new Pair<FunctionSymbol,FunctionSymbol>(f, g);
    return null;
  }

  /**
   * This returns a function symbol f so that arguments a1...an exist such that:
   * - f(a1,...,an) has type otype
   * - f has rule arity > n + numargs
   * - f is not h (note that h is allowed to be null, in which case nothing is excluded)
   * If such a function symbol f does not exist, then null is returned instead.
   */
  private static FunctionSymbol findSemiConstructor(ProofContext context,
                                                    Type otype, int numargs, FunctionSymbol h) {
    int oar = otype.queryArity();
    for (FunctionSymbol f : context.getTRS().queryAlphabet().getSymbols()) {
      // check: f != h
      if (f == h) continue;
      // compute n knowing that IF f(a1,...,an) :: otype, then arity(f) = n + arity(otype),
      // so n = arity(f) - arity(otype) ≥ 0
      Type t = f.queryType();
      int k = t.queryArity();
      if (k < oar) continue;
      int n = k - oar;
      // check: f has rule arity > n + numargs
      if (context.queryRuleArity(f) <= n + numargs) continue;
      // check: the type of f(a1,...,an) is indeed otype
      for (int i = 0; i < n; i++) t = t.subtype(2);
      if (t.equals(otype)) return f;
    }
    return null;
  }

  @Override
  public boolean verify(Optional<OutputModule> m) {
    // we need to make sure that the equation we're looking at is actually complete
    int index = _equ.getIndex();
    if (_state.getIncompleteEquations().contains(index)) {
      m.ifPresent(o -> o.println("DISPROVE can only be applied on complete equation contexts."));
      return false;
    }
    return true;
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    return ProofState.getContradictionState();
  }

  @Override
  public String commandDescription() {
    return "disprove";
  }

  @Override
  public void explain(OutputModule module) {
    String extra1 = _left.queryType().equals(_equ.getEquation().getLhs().queryType()) ? "" : "(...)";
    String extra2 = _right.queryType().equals(_equ.getEquation().getRhs().queryType()) ? "" : "(...)";
    module.println("We apply DISPROVE to %a, which succeeds because the sides can be " +
      "instantiated to distinct semi-constructor terms; respectively %a%a and %a%a.",
        _equ.getName(), _left.queryName(), extra1, _right.queryName(), extra2);
  }
}

