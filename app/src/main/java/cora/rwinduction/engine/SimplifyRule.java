package cora.rwinduction.engine;

import charlie.terms.Substitution;
import charlie.terms.position.Position;
import charlie.trs.Rule;
import org.jetbrains.annotations.NotNull;

import java.util.Objects;

class SimplifyRule {

  public final class SimplifyArgs extends RuleArguments {

    private final EqSide _side;

    private final Rule _simplRule;

    private final Position _position;

    private final Substitution _matchingSubstitution;

    private final Substitution _freeVariableSubstitution;

    public SimplifyArgs(@NotNull ProofState proofState,
                              @NotNull int eqIndex,
                              @NotNull EqSide s,
                              @NotNull Rule rule,
                              @NotNull Position p,
                              @NotNull Substitution matchingSubstitution,
                              @NotNull Substitution freeVariableSubstitution) {
      super(proofState, eqIndex);
      Objects.requireNonNull(proofState);
      Objects.requireNonNull(s);
      Objects.requireNonNull(rule);
      Objects.requireNonNull(p);
      Objects.requireNonNull(matchingSubstitution);
      Objects.requireNonNull(freeVariableSubstitution);

      _side = s;
      _simplRule = rule;
      _position = p;
      _matchingSubstitution = matchingSubstitution;
      _freeVariableSubstitution = freeVariableSubstitution;
    }

    public Position getPosition() {
      return _position;
    }

    public Substitution getMatchingSubstitution() {
      return _matchingSubstitution;
    }
    public EqSide getSide() {
      return _side;
    }

    public Rule getRule() {
      return _simplRule;
    }

    public Substitution getFreeVariableSubstitution() {
      return _freeVariableSubstitution;
    }
  }

  // Here's the list of checks we need to do in order to apply this rule to an equation
  // s = t [d]
  /*
    - Check that the rule given as argument is a rule in R or H.
    - Check that the given position p and substitution Gamma satisfies:
        s|_p = l Gamma
    - Check that Gamma(LVar(l -> r [c]) is contained in Val \cup Vars(d)
    - Check that the Implication c => d Gamma
    - The user may provide an extention of Gamma, let's call it Delta,
    - if so check all the conditions again with the composition Gamma . Delta
   */

  // Implementation of each checking, individually ------------------------------------------------



  // ----------------------------------------------------------------------------------------------


//  /**
//   * @param args
//   * @param <T>
//   * @return
//   */
//  @Override
//  <T extends RuleArguments> Either<String, Unit> isApplicable(T args) {
//    return null;
//  }
//
//  /**
//   * @param args
//   * @param <T>
//   * @return
//   */
//  @Override
//  protected <T extends RuleArguments> ProofState ruleLogic(T args) {
//    return null;
//  }

}
