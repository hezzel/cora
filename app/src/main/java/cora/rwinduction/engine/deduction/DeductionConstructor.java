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

public final class DeductionConstructor extends DeductionStep {
  private DeductionConstructor(ProofState state, ProofContext context) {
    super(state, context);
  }
 
  public static Optional<DeductionConstructor> createStep(PartialProof proof,
                                                          Optional<OutputModule> module) {
    ProofState state = proof.getProofState();
    Equation eq = DeductionStep.getTopEquation(state, module);
    if (eq == null) return Optional.empty();
    if (!eq.getLhs().isFunctionalTerm() || !eq.getRhs().isFunctionalTerm()) {
      module.ifPresent(o -> o.println("The semiconstructor rule can only be applied if both " +
        "sides of the equation are functional terms.  (Use \"context\" for the more general " +
        "case, which does, however, lose completeness.)"));
      return Optional.empty();
    }
    if (!eq.getLhs().queryRoot().equals(eq.getRhs().queryRoot())) {
      module.ifPresent(o -> o.println("The semiconstructor rule cannot be applied, because the " +
        "two sides of the equation do not have the same root symbol."));
      return Optional.empty();
    }
    if (eq.getLhs().numberArguments() != eq.getRhs().numberArguments()) {
      module.ifPresent(o -> o.println("The semiconstructor rule cannot be applied, because the " +
        "two sides of the equation do not have the same number of arguments."));
      return Optional.empty();
    }
    return Optional.of(new DeductionConstructor(state, proof.getContext()));
  }

  /**
   * This verifies that the root symbols on both sides of the top equation are in fact constructors
   * or partially applied function symbols.
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    FunctionSymbol f = _equ.getEquation().getLhs().queryRoot();
    int n = _equ.getEquation().getLhs().numberArguments();
    int k = _pcontext.queryRuleArity(f);
    if (n >= k) {
      println(module, "The semiconstructor rule cannot be applied, because %a is a %a symbol " +
        "with enough arguments.", f, f.isTheorySymbol() ? "calculation" : "defined");
      return false;
    }
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
    return "semiconstructor";
  }

  @Override
  public void explain(OutputModule module) {
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

