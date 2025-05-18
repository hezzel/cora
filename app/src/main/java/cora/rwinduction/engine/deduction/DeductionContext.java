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

import java.util.ArrayList;
import java.util.Optional;
import charlie.terms.*;
import charlie.printer.Printer;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This class handles both the SEMICONSTRUCTOR and APPLICATION commands, both of which cut up an
 * equation f s1 ... sn = f t1 ... tn into (s1,t1), ..., (sn,tn), but differ in whether f should be
 * a constructor or partially applied function symbol (SEMICONSTRUCTOR), or an arbitrary head,
 * including variables and defined symbols (APPLICATION).  The former is a complete step; the latter
 * is not.
 */
public final class DeductionContext extends DeductionStep {
  private boolean _complete;

  private DeductionContext(ProofState state, ProofContext context, boolean complete) {
    super(state, context);
    _complete = complete;
  }
 
  public static Optional<DeductionContext> createStep(PartialProof proof,
                                                      Optional<OutputModule> module,
                                                      boolean shouldBeComplete) {
    ProofState state = proof.getProofState();
    Equation eq = DeductionStep.getTopEquation(state, module);
    if (eq == null) return Optional.empty();

    String name = shouldBeComplete ? "semiconstructor" : "application";

    if (!eq.getLhs().queryHead().equals(eq.getRhs().queryHead())) {
      module.ifPresent(o -> o.println("The " + name + " rule cannot be applied, because the " +
        "two sides of the equation do not have the same head."));
      return Optional.empty();
    }
    if (eq.getLhs().numberArguments() != eq.getRhs().numberArguments()) {
      module.ifPresent(o -> o.println("The " + name + " rule cannot be applied, because the " +
        "two sides of the equation do not have the same number of arguments."));
      return Optional.empty();
    }

    boolean isComplete = checkCompleteness(eq, proof.getContext());
    if (shouldBeComplete && !isComplete) {
      module.ifPresent(o -> o.println("The semiconstructor rule can only be applied if both " +
        "sides of the equation have a form f s1 ... sn, with f a function symbol and n < ar(f).  " +
        "(Use \"application\" for the more general form, which does, however, lose " +
        "completeness.)"));
      return Optional.empty();
    }

    return Optional.of(new DeductionContext(state, proof.getContext(), isComplete));
  }

  /**
   * Helper function for createStep: this checks if we really have an application of SEMICONSTRUCTOR
   * or one of APPLICATION.
   */
  private static boolean checkCompleteness(Equation equation, ProofContext pcontext) {
    Term left = equation.getLhs();
    if (!left.isFunctionalTerm()) return false;
    FunctionSymbol f = left.queryRoot();
    int n = left.numberArguments();
    int k = pcontext.queryRuleArity(f);
    return n < k;
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    return true;
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Term left = _equ.getEquation().getLhs();
    Term right = _equ.getEquation().getRhs();
    Term constr = _equ.getEquation().getConstraint();
    int n = left.numberArguments();
    ArrayList<EquationContext> neweqs = new ArrayList<EquationContext>();
    int index = _state.getLastUsedIndex();
    for (int i = n; i >= 1; i--) {
      Equation newequation = new Equation(left.queryArgument(i), right.queryArgument(i), constr);
      index++;
      neweqs.add(_equ.replace(newequation, index));
    }
    return _state.replaceTopEquation(neweqs);
  }

  @Override
  public String commandDescription() {
    return _complete ? "semiconstructor" : "application";
  }

  @Override
  public void explain(OutputModule module) {
    if (!_complete) {
      module.println("We apply APPLICATION to %a, splitting the immediate arguments into " +
        "separate equations.", _equ.getName());
      return;
    }
    FunctionSymbol f = _equ.getEquation().getLhs().queryRoot();
    if (_pcontext.getTRS().isDefined(f) || f.toCalculationSymbol() != null) {
      module.println("We apply SEMICONSTRUCTOR to %a, since the rule arity of %a is %a and only " +
        "%a arguments are present.", _equ.getName(), f, _pcontext.queryRuleArity(f),
        _equ.getEquation().getLhs().numberArguments());
    }
    else module.println("We apply SEMICONSTRUCTOR to %a since %a is a constructor symbol.",
      _equ.getName(), f.queryName());
  }
}

