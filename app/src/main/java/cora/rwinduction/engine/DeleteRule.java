package cora.rwinduction.engine;

import charlie.theorytranslation.TermAnalyser;
import charlie.trs.Rule;
import cora.config.Settings;

public class DeleteRule extends DeductionRule {

  class DeleteArgs extends RuleArguments {
    public int test;
  }

  /**
   * The <b>delete</b> deduction rule can be applied whenever either the selected equation
   * {@code s = t [c]} is such that {@code s} is syntactically
   * (which means modulo-alpha when lambdas are present)
   * identical to {@code t} or the constraint {@code c} is not satisfiable.
   *
   * @param proofState The input proof state, it has the form of a pair (E, H) of equations and
   *                   hypotheses.
   * @param equationIndex The index of an equation in E, for which <b>delete</b> should be
   *                      applied to.
   *
   */
  @Override
  public boolean isApplicable(ProofState proofState, int equationIndex) {
    Equation equation = proofState.getEquations().get(equationIndex);

    boolean constraintIsUnsatisfiable = false;

    TermAnalyser.Result res =
      TermAnalyser.satisfy(equation.getConstraint(), Settings.smtSolver);

    switch (res) {
      case TermAnalyser.Result.YES(_):
        break;

      case TermAnalyser.Result.NO() :
        constraintIsUnsatisfiable = true;
        break;

      case TermAnalyser.Result.MAYBE(String reason):
        System.out.println(reason);
        break;
    }

    return equation.getLhs().equals(equation.getRhs()) || constraintIsUnsatisfiable;
  }

  /**
   * @param proofState
   * @param equationIndex
   * @return
   */
  @Override
  ProofState ruleLogic(ProofState proofState, int equationIndex) {
    return null;
  }

  ProofState ruleLogic(ProofState proofState, int equationIndex, int tes) {
    return null;
  }



}
