package cora.rwinduction.engine;

import charlie.reader.CoraInputReader;
import charlie.terms.Renaming;
import charlie.terms.Term;
import charlie.trs.TRS;
import charlie.util.Pair;
import charlie.util.either.Either;
import com.google.common.collect.ImmutableList;
import cora.io.DefaultOutputModule;
import cora.io.OutputModule;
import cora.rwinduction.engine.data.Equation;
import cora.rwinduction.engine.data.ProofState;
import cora.rwinduction.engine.data.ProverContext;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

class CommandDeleteTest {

  TRS trs = CoraInputReader.readTrsFromString (
    "sum :: Int -> Int\n" +
      "sum(x) -> 0         | x ≤ 0\n" +
      "sum(x) -> x + sum(x - 1) | x > 0"
  );

  OutputModule outputModule =
    DefaultOutputModule.createUnicodeModule(trs);

  Term lhs = CoraInputReader.readTerm("0", trs);
  Term rhs = CoraInputReader.readTerm("0", trs);
  Term ctr = CoraInputReader.readTerm("true", trs);
  Renaming eqRenaming =
    outputModule.queryTermPrinter().generateUniqueNaming(lhs, rhs, ctr);
  Equation eq = new Equation(lhs, rhs, ctr, eqRenaming);

  Prover prover =
    new Prover(new ProverContext(trs, ImmutableList.of(eq), outputModule));

  CommandDelete command = new CommandDelete();

  @Test
  void numberOfEquationsReduceByOneTest() {

    int beforeCmdRun = prover
      .getProverContext()
      .getProofState()
      .getEquations()
      .size();

    Either<String, Boolean> result =
      command.run(prover, "delete");

    int afterCmdRun = prover
      .getProverContext()
      .getProofState()
      .getEquations()
      .size();

    assertTrue(result.isRight());
    assertEquals(afterCmdRun, beforeCmdRun - 1);
  }

  @Test
  void testConstraintUnsatisfiable() {
    // When the constraint is unsatisfiable
    Term lhs1 = CoraInputReader.readTerm("1", trs);
    Term rhs1 = CoraInputReader.readTerm("2", trs);
    Term ctr1 = CoraInputReader.readTerm("0 > 0", trs);
    Equation eq1 = new Equation(lhs1, rhs1, ctr1, eqRenaming);

    System.out.println(prover.getProverContext().getProofState().getEquations().size());

    prover
      .getProverContext()
      .addProofStep(
        prover.getProverContext().getProofState().addEquation(eq1),
        "lemma 1 = 2 | 1 > 0"
      );

    System.out.println(prover.getProverContext().getProofState().getEquations().size());

    Pair<ProofState, String> proofStep =
      prover.getProverContext().getProofStep();

    System.out.println(proofStep);


  }

  // TODO add more tests
}
