package cora.rwinduction.engine;

import charlie.terms.Substitution;
import charlie.theorytranslation.TermAnalyser;
import charlie.util.either.Either;
import charlie.util.either.FunctorialUtils;
import charlie.util.either.Left;
import charlie.util.either.Right;
import cora.config.Settings;
import org.jetbrains.annotations.NotNull;
import java.util.stream.Stream;

final class DeleteRule extends DeductionRule {

  /**
   * In an equation of the form {@code s = t [c]}, this method checks if {@code c}
   * is unsatisfiable.
   *
   * @return returns {@code Left<String> reason} if the equation is either satisfiable or the SMT
   * solver returned a maybe, which in this case we pass the SMT's reason for that through.
   * In case the equation is <b>unsat</b>, it returns {@code}
   */
  static Either<String, Boolean> checkEqConstraint(Equation equation) {

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
  Either<String, Boolean> isLeftEqualsRight(Equation equation) {
    return new Right<>(equation.getLhs().equals(equation.getRhs()));
  }

  @Override
  public <T extends RuleArguments> Either<String, Boolean> isApplicable(@NotNull T args) {

    // Check if the equation index is within bounds.
    // Note: this test should've been done before.
    // But I don't trust people will really do it always.
    Either<String, Boolean> checkEqBounds = args.checkEqBounds();

    return switch (checkEqBounds) {
      case Left<String, Boolean>  _ -> checkEqBounds;

      case Right<String, Boolean> _ -> {
        // Check if the constraint in the equation is unsatisfiable.
        Equation equation = args.getProofState()
          .getEquations()
          .get(args.getEquationIndex());
        Either<String, Boolean> isUnsat = checkEqConstraint(equation);

        // Check if, in the equation, s = t [c] s is syntactically equal to t
        Either<String, Boolean> leftRightSyntaxEq = isLeftEqualsRight(equation);

        yield Stream
          .of(isUnsat, leftRightSyntaxEq)
          .reduce(
            FunctorialUtils.pure(false),
            FunctorialUtils.liftBinOp( (x, y) -> x || y)
          );
      }
    };
  }

  @Override
  public <T extends RuleArguments> Either<String, ProofState> ruleLogic(@NotNull T args) {
    return new Right<>(args.getProofState().deleteEquation(args.getEquationIndex()));
  }
}
