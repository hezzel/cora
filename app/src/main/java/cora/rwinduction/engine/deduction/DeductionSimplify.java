package cora.rwinduction.engine.deduction;

import charlie.exceptions.IndexingException;
import charlie.terms.*;
import charlie.terms.position.Position;
import charlie.theorytranslation.TermSmtTranslator;
import charlie.trs.Rule;
import charlie.util.either.Either;
import charlie.util.either.Left;
import charlie.util.either.Right;
import com.google.common.collect.ImmutableList;
import cora.config.Settings;
import cora.rwinduction.engine.data.Equation;
import cora.rwinduction.engine.data.ProofState;
import org.jetbrains.annotations.NotNull;
import java.util.Objects;

class DeductionSimplify extends DeductionAbstractRule {

  static final class SimplifyArgs extends DeductionArguments {

    private final EqSide _side;
    private final Either<Integer, Integer> _simplRule;
    private final Position _position;
    private final Substitution _matchingSubstitution;
    private final Renaming _newNaming;

    /**
     * The rule simplify requires the following arguments.
     *
     * @param proofState the input proof state, of type {@link ProofState}, of the shape {@code
     * (E, H)}.
     * @param eqIndex the index of the equation this rule will be applied to
     * @param s the equation side for which this rule will be applied, i.e.,
     * {@link DeductionArguments.EqSide#L } for left or
     * {@link DeductionArguments.EqSide#R } for right.
     *
     * @param rule the index of the to be in either R or H, pass a {@link charlie.util.either.Left}
     *             in the former or a {@link charlie.util.either.Right} on the latter case.
     * @param p the position for which the rule will be applied to
     * @param matchingSubstitution the matching substitution.
     */
    public SimplifyArgs(@NotNull ProofState proofState,
                        @NotNull int eqIndex,
                        @NotNull EqSide s,
                        @NotNull Either<Integer, Integer> rule,
                        @NotNull Position p,
                        @NotNull Substitution matchingSubstitution,
                        @NotNull Renaming newNaming) {
      super(proofState, eqIndex);
      Objects.requireNonNull(proofState);
      Objects.requireNonNull(s);
      Objects.requireNonNull(rule);
      Objects.requireNonNull(p);
      Objects.requireNonNull(matchingSubstitution);
      Objects.requireNonNull(newNaming);

      _side = s;
      _simplRule = rule;
      _position = p;
      _matchingSubstitution = matchingSubstitution;
      _newNaming = newNaming;
    }

    /** Returns the position */
    public Position getPosition() { return _position; }

    public Substitution getMatchingSubstitution() { return _matchingSubstitution; }

    public EqSide getSide() { return _side; }

    /**
     * Given a proof state (E, H).
     * This value represents the choice of the rewriting rule from either the TRS R or a
     * hypothesis on H.
     *
     * @apiNote Every instance of {@link ProofState} carries a reference to a TRS, which is
     * accessible via {@link ProofState#getTRS()}.
     */
    public Either<Integer, Integer> getRuleIndex() { return _simplRule; }

    /**
     * Returns the chosen rewrite rule from either the TRS or the hypothesis.
     *
     * @throws IndexingException if the index chosen is out of bounds.
     */
    public Rule getRwRule() {
      return
        switch (this.getRuleIndex()) {
        case Left<Integer, Integer>(Integer index) ->
          this.getProofState().getTRS().queryRule(index);
        case Right<Integer, Integer>(Integer index) ->
          this.getProofState().getHypotheses().get(index);
      };
    }

    public Term getMatchingTerm() {
      Equation currEq = this
        .getProofState()
        .getEquations()
        .get(this.getEquationIndex());

      return
        switch (_side) {
          case L -> currEq.getLhs();
          case R -> currEq.getRhs();
        };
    }
  }

  /*
   Checklist of conditions we need to verify in order to apply this rule to an equation
   s = t [d]

  - the rule given as argument is a rule in R or H,
  - the given position p and substitution Gamma satisfies s|_p = l Gamma,
  - Gamma(LVar(l -> r [c]) is contained in Val \cup Vars(d), and
  - check that the implication c => d Gamma is valid.
  */

  // Implementation of each checking, individually ------------------------------------------------
  // TODO The errors messages here can be improved with more detailed information.

  private static Either<String, Boolean> checkIndexBounds(SimplifyArgs args) {
    // check bounds for equations
    Either<String, Boolean> checkEq = args.checkEqBounds();
    if(checkEq.isLeft()) { return checkEq; }

    // check bounds for rewrite rules or hypothesis bounds
    Either<String, Boolean> checkRule =
      switch (args.getRuleIndex()) {
        case Left<Integer, Integer>(Integer index) -> {
          try {
            args.getProofState().getTRS().queryRule(index);
            yield new Right<>(true);
          } catch (IndexingException e) {
            yield new Left<>(e.toString());
          }
        }
        case Right<Integer, Integer>(Integer index) -> args.checkHypBounds(index);
      };

    if(checkRule.isLeft()) { return checkRule; }

    return new Right<>(true);
  }

  private static Either<String, Boolean> checkMatching(SimplifyArgs args) {
      Term sideOnP =
        args.getMatchingTerm().querySubterm(args.getPosition());

      Term lhsInstance =
        args.getRwRule().queryLeftSide().substitute(args.getMatchingSubstitution());

      if (sideOnP.equals(lhsInstance)) {
        return new Right<>(true);
      } else {
        return new Left<>("Failed to apply this rule. Matching substitution does not match.");
      }
  }

  private static Either<String, Boolean> checkLVars(SimplifyArgs args) {
    ImmutableList<Variable> lVars = args
      .getRwRule()
      .queryLVars();
    ImmutableList<Term> substImage = lVars
      .stream()
      .map(x -> args.getMatchingSubstitution().getReplacement(x))
      .collect(ImmutableList.toImmutableList());
    Environment<Variable> cVars = args
      .getProofState()
      .getEquations()
      .get(args.getEquationIndex())
      .getConstraint()
      .vars();

    Boolean result = substImage
      .stream()
      .allMatch(x -> x.isValue() || cVars.contains((Variable) x));

    if (result) {
      return new Right<>(true);
    } else {
      return new Left<>("Failed to apply this rule. LVARS.");
    }
  }

  private static Either<String, Boolean> checkImplication(SimplifyArgs args) {
    Equation currEq = args
      .getProofState()
      .getEquations()
      .get(args.getEquationIndex());

    Term ruleCtrsInstantiation =
      args.getRwRule().queryConstraint().substitute(args.getMatchingSubstitution());

    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(currEq.getConstraint(), ruleCtrsInstantiation);

     boolean isValid = Settings.smtSolver.checkValidity(translator.queryProblem());

     if(isValid) {
       return new Right<>(true);
     } else {
       return new Left<>("Validity check of constraint failed.");
     }
  }

  // ----------------------------------------------------------------------------------------------

  /**
   *
   * @param args
   * @param <T>
   * @return
   */
  @Override
  <T extends DeductionArguments> Either<String, Boolean> isApplicable(T args) {
    if (args instanceof SimplifyArgs simplifyArgs) {
      Either<String, Boolean> bounds = checkIndexBounds(simplifyArgs);
      if (bounds.isLeft()) { return bounds; }

      Either<String, Boolean> checkMatching = checkMatching(simplifyArgs);
      if (checkMatching.isLeft()) { return checkMatching; }

      Either<String, Boolean> checkLVars = checkLVars(simplifyArgs);
      if (checkLVars.isLeft()) { return checkLVars; }

      Either<String, Boolean> checkImplication = checkImplication(simplifyArgs);
      if (checkImplication.isLeft()) { return checkImplication; }

      return new Right<>(true);
    } else {
      return new Left<>("Argument object should be of type SimplifyArgs.");
    }
  }

  /**
   * @param args
   * @param <T>
   * @return
   */
  @Override
  protected <T extends DeductionArguments> Either<String, ProofState> ruleLogic(T args) {
    if (args instanceof SimplifyArgs simplifyArgs) {
      Term rhsRuleInstance = simplifyArgs
        .getRwRule()
        .queryRightSide()
        .substitute(simplifyArgs.getMatchingSubstitution());

      Equation currEq = simplifyArgs
        .getProofState()
        .getEquations()
        .get(simplifyArgs.getEquationIndex());

      Equation newEquation =
        switch (simplifyArgs.getSide()) {
        case L -> {
            Term newLeft =
              currEq.getLhs().replaceSubterm(simplifyArgs.getPosition(), rhsRuleInstance);
            yield new Equation(newLeft, currEq.getRhs(), currEq.getConstraint());
          }
          case R -> {
            Term newRight =
              currEq.getRhs().replaceSubterm(simplifyArgs.getPosition(), rhsRuleInstance);
            yield new Equation(currEq.getLhs(), newRight, currEq.getConstraint());
          }
        };

      ProofState newProofState = simplifyArgs
        .getProofState()
        .replaceEquation(simplifyArgs.getEquationIndex(), newEquation);

      return new Right<>(newProofState);
    } else {
      return new Left<>("Argument object should be of type SimplifyArgs.");
    }
  }
}
