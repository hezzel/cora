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
import charlie.terms.Term;
import charlie.terms.Value;
import charlie.terms.TheoryFactory;
import charlie.substitution.Substitution;
import charlie.substitution.MutableSubstitution;
import charlie.printer.PrinterFactory;
import charlie.printer.Printer;
import charlie.theorytranslation.TermAnalyser;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This deduction step handles the theory case of the disprove command, where the user supplies a
 * ground substitution such that sγ != tγ yet φγ is satisfied.
 */
public class DeductionDisproveTheory extends DeductionStep {
  protected Substitution _substitution;

  protected DeductionDisproveTheory(ProofState state, ProofContext context, Substitution subst) {
    super(state, context);
    _substitution = subst;
  }

  /**
   * Create a theory disprove step.  The given substitution must map all variables in the top
   * equation to ground theory terms.  The substitution will become property of the created step,
   * so should not be changed afterwards.
   */
  public static DeductionDisproveTheory createStep(PartialProof proof, Optional<OutputModule> m,
                                                   Substitution subst) {
    ProofState state = proof.getProofState();
    ProofContext context = proof.getContext();
    Equation equation = getTopEquation(proof.getProofState(), m); 
    if (equation == null) return null;

    if (state.getIncompleteEquations().contains(state.getTopEquation().getIndex())) {
      m.ifPresent(o -> o.println("DISPROVE can only be applied on complete equation contexts."));
      return null;
    }

    Term left = subst.substitute(equation.getLhs());
    Term right = subst.substitute(equation.getRhs());
    Term constr = subst.substitute(equation.getConstraint());
    if (!left.isGround() || !right.isGround() || !constr.isGround() || !constr.isTheoryTerm()) {
      m.ifPresent(o -> o.println("The substitution does not map all variables in the equation " +
        "to ground theory terms."));
      return null;
    }
    if (!left.isTheoryTerm() || !right.isTheoryTerm() ||
        !left.queryType().isBaseType() | !right.queryType().isBaseType()) {
      m.ifPresent(o -> o.println("The left- and right-hand sides of the equation do not have " +
        "base type."));
      return null;
    }

    return new DeductionDisproveTheory(state, context, subst);
  }

  @Override
  public final ProofState tryApply(Optional<OutputModule> module) {
    return ProofState.getContradictionState();
  }

  @Override
  public final String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("disprove theory with ");
    printer.add(printer.makePrintable(_substitution, _equ.getRenaming(), _equ.getRenaming()));
    return printer.toString();
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    Value constraint = TermAnalyser.evaluate(_substitution.substitute(_equ.getConstraint()));
    Value l = TermAnalyser.evaluate(_substitution.substitute(_equ.getLhs()));
    Value r = TermAnalyser.evaluate(_substitution.substitute(_equ.getRhs()));
    if (!constraint.equals(TheoryFactory.trueValue)) {
      println(module, "DISPROVE cannot be applied with the given substitution %a, since the " +
        "instantiated constraint evaluates to false.",
        Printer.makePrintable(_substitution, _equ.getRenaming(), _equ.getRenaming()));
      return false;
    }
    if (l.equals(r)) {
      println(module, "DISPROVE cannot be applied with the given substitution, since the " +
        "instantiated left- and right-hand side both evaluate to %a.", l);
      return false;
    }
    return true;
  }

  @Override
  public void explain(OutputModule module) {
    Value constraint = TermAnalyser.evaluate(_substitution.substitute(_equ.getConstraint()));
    Value l = TermAnalyser.evaluate(_substitution.substitute(_equ.getLhs()));
    Value r = TermAnalyser.evaluate(_substitution.substitute(_equ.getRhs()));
    module.println("We apply DISPROVE to %a, which succeeds because under the substitution %a, " +
      "the constraint %a evaluates to true, while the sides of the equation can be calculated " +
      "to %a and %a respectively.", _equ.getName(),
      Printer.makePrintable(_substitution, _equ.getRenaming(), _equ.getRenaming()),
      Printer.makePrintable(_equ.getEquation().getConstraint(), _equ.getRenaming()), l, r);
  }
}

