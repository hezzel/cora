package cora.rwinduction.engine;

import charlie.reader.CoraInputReader;
import charlie.terms.Term;
import charlie.trs.TRS;
import charlie.util.either.Either;
import com.google.common.collect.ImmutableList;
import org.junit.jupiter.api.Test;

class DeleteRuleTest {

  DeleteRule deleteRule = new DeleteRule();

  @Test
  void testIsApplicableOutOfBounds() {
    TRS trs = CoraInputReader.readTrsFromString(
      "sum :: Int -> Int " +
      "sum(x) -> 0         | x ≤ 0 " +
      "sum(x) -> x + sum(x - 1) | x > 0"
    );

    Term lhs = CoraInputReader.readTerm("sum(n)", trs);
    Term rhs = CoraInputReader.readTerm("n * (n + 1) / 2", trs);
    Term ctr = CoraInputReader.readTerm("n > 0 /\\ n < 0", trs);
    Equation eq = new Equation(lhs, rhs, ctr);

    ProofState proofState = new ProofState(ImmutableList.of(eq));

    RuleArguments ruleArguments = new RuleArguments(proofState, 0);

    Either<String, Boolean> checkCtr = DeleteRule.checkEqConstraint(eq);

    Either<String, ProofState> res = deleteRule.applyRule(ruleArguments);

    System.out.println(res);

  }
}
