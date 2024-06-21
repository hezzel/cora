package cora.rwinduction.engine;

import charlie.terms.Substitution;
import charlie.theorytranslation.TermAnalyser;
import charlie.util.either.Either;
import charlie.util.either.FunctorialUtils;
import charlie.util.either.Left;
import charlie.util.either.Right;
import cora.config.Settings;
import org.jetbrains.annotations.NotNull;
import java.util.function.BinaryOperator;


final class DeleteRule extends DeductionRule {

  /**
   * In an equation of the form {@code s = t [c]}, this method checks if {@code c}
   * is unsatisfiable.
   *
   * @return returns {@code Left<String> reason} if the equation is either satisfiable or the SMT
   * solver returned a maybe, which in this case we pass the SMT's reason for that through.
   * In case the equation is <b>unsat</b>, it returns {@code}
   */
  private static Either<String, Boolean> checkEqConstraint(Equation equation) {

    TermAnalyser.Result res =
      TermAnalyser.satisfy(equation.getConstraint(), Settings.smtSolver);

    return switch (res) {
      case TermAnalyser.Result.YES(Substitution val) ->
        new Left<>("The equation is satisfiable by the valuation : " + val.toString());

      case TermAnalyser.Result.NO() ->
        new Right<>(true);

      case TermAnalyser.Result.MAYBE(String reason) ->
        new Left<>(reason);
    };
  }

  /**
   * TODO write documentation
   * @param equation
   * @return
   */
  private static Either<String, Boolean> isLeftEqualsRight(Equation equation) {
    return new Right<>(equation.getLhs().equals(equation.getRhs()));
  }


  @Override
  public <T extends RuleArguments> Either<String, Boolean> isApplicable(@NotNull T args) {
    // For efficiency, after checking each condition, if they fail (so returning a Left<>)
    // We should return its value immediately and don't check the other conditions.
    // Implementation note: specially the ones that use the SMT solvers.
    // Do those tests only after all the others didn't fail.
    Either<String, Boolean> checkEqBounds = args.checkEqBounds();
    if (checkEqBounds.isLeft()) { return checkEqBounds; }

    // Get the equation
    Equation equation = args.getProofState()
      .getEquations()
      .get(args.getEquationIndex());

    // Check if s is syntactically equal to t in the equation s = t [c].
    Either<String, Boolean> leftRightSyntaxEq = isLeftEqualsRight(equation);
    if (leftRightSyntaxEq.isLeft()) { return leftRightSyntaxEq; }

    // !(SMT usage) Check if the constraint in the equation is unsatisfiable.
    Either<String, Boolean> isUnsat = checkEqConstraint(equation);
    if (isUnsat.isLeft()) { return isUnsat; }

    // Whenever none of the tests fail, we return their disjunction.
    BinaryOperator<Either<String, Boolean>> liftedOp =
      FunctorialUtils.liftBinOp((x, y) -> x || y);

    return liftedOp.apply(isUnsat, leftRightSyntaxEq);
  }

  @Override
  protected <T extends RuleArguments> Either<String, ProofState> ruleLogic(@NotNull T args) {
    return new Right<>(args.getProofState().deleteEquation(args.getEquationIndex()));
  }
}