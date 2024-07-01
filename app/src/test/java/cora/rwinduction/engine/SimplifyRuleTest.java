package cora.rwinduction.engine;

import charlie.reader.CoraInputReader;
import charlie.terms.Substitution;
import charlie.terms.Term;
import charlie.terms.TermFactory;
import charlie.terms.position.Position;
import charlie.trs.TRS;
import charlie.util.either.Left;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.Test;

class SimplifyRuleTest {

  SimplifyRule simplifyRule = new SimplifyRule();
  TRS trs = CoraInputReader.readTrsFromString(
    "sum :: Int -> Int " +
      "sum(x) -> 0         | x ≤ 0 " +
      "sum(x) -> x + sum(x - 1) | x > 0"
  );
  Term lhs = CoraInputReader.readTerm("sum(n)", trs);
  Term rhs = CoraInputReader.readTerm("n * (n + 1) / 2", trs);
  Term ctr = CoraInputReader.readTerm("n > 0 /\\ n < 0", trs);
  Equation eq = new Equation(lhs, rhs, ctr);

  @Test
  void isApplicable() {
    ProofState proofState = new ProofState(trs, ImmutableList.of(eq));
    Position p = Position.empty;
    Substitution s = TermFactory.createEmptySubstitution();

    SimplifyRule.SimplifyArgs args =
      new SimplifyRule.SimplifyArgs (
        proofState,
        0,
        RuleArguments.EqSide.L,
        new Left<>(0),
        p,
        s);

    System.out.println(simplifyRule.isApplicable(args));
  }

  @Test
  void ruleLogic() {
  }
}
