package cora.rwinduction.engine;

import charlie.exceptions.IndexingException;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import org.jetbrains.annotations.NotNull;

final class DeleteRule extends DeductionRule {

  /**
   * The <b>delete</b> deduction rule can be applied whenever either the selected equation
   * {@code s = t [c]} is such that {@code s} is syntactically
   * (which means modulo-alpha when lambdas are present)
   * identical to {@code t} or the constraint {@code c} is not satisfiable.
   *
   * @param args default parent class {@link RuleArguments} since this rule doesn't need
   *             additional parameters.
   *             Therefore, this method expects {@code args} to be of type {@code RuleArguments}.
   *
   * @return whether delete can be applied to the selected equation
   *
   * @throws IndexingException if rule index given in args is out of bounds.
   */
  @Override
  public <T extends RuleArguments> boolean isApplicable(@NotNull T args) {

    if(args.getRuleIndex() >= args.getProofState().getEquations().size()) {
      throw new IndexingException(
        "DeleteRule",
        "isApplicable",
        args.getRuleIndex()
      );
    }

    Equation equation = args.getProofState()
      .getEquations()
      .get(args.getRuleIndex());

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

  @Override
  public <T extends RuleArguments> ProofState ruleLogic(@NotNull T args) {
    return args.getProofState().deleteEquation(args.getRuleIndex());
  }

}
