package cora.termination.dependency_pairs.processors;

import charlie.reader.CoraInputReader;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.trs.TRS;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ChainingProcessorTest {


  private static TRS makeTRSWithOneRecDP() {
    return CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
        "f(x, y) -> f(x, y-1) | x < y ∧ x > 42"
    );
  }

  private static TRS makeTRSWithOneNonRecDP() {
    return CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
        "g :: Int -> Int -> Int\n" +
        "h :: Int -> Int -> Int\n" +
        "f(x, y) -> g(x, y-1) | x < y ∧ y > 42\n" +
        "g(x, y) -> h(x+7, 3*y) | x < y ∧ y > 42"
    );
  }

  private static TRS makeTRSWithTwoDPsChain() {
    return CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
        "g :: Int -> Int -> Int\n" +
        "h :: Int -> Int -> Int\n" +
        "i :: Int -> Int -> Int\n" +
        "f(x, y) -> g(x, y-1) | x < y ∧ y > 42\n" +
        "g(x, y) -> h(x+7, 3*y) | x < y ∧ y > 8\n" +
        "h(u, v) -> i(u, v)"
    );
  }


  private static TRS makeTRSWithThreeDPsCycle() {
    return CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
        "g :: Int -> Int -> Int\n" +
        "h :: Int -> Int -> Int\n" +
        "f(x, y) -> g(x, y-1) | x < y ∧ y > 42\n" +
        "g(x, y) -> h(x+7, 3*y) | x < y ∧ y > 42\n" +
        "h(u, v) -> f(u, v)"
    );
  }

  @Test
  public void testOneNonRecDPNoSelfChaining() {
    TRS trs = makeTRSWithOneNonRecDP();
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    ChainingProcessor proc = new ChainingProcessor(false);
    assertFalse(proc.isApplicable(p));
    ProcessorProofObject proof = proc.processDPP(p);
    assertFalse(proof.applicable());
  }

  @Test
  public void testOneNonRecDPWithSelfChaining() {
    TRS trs = makeTRSWithOneNonRecDP();
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    ChainingProcessor proc = new ChainingProcessor(true);
    ProcessorProofObject proof = proc.processDPP(p);
    assertFalse(proof.applicable());
  }

  @Test
  public void testOneRecDPNoSelfChaining() {
    TRS trs = makeTRSWithOneRecDP();
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    ChainingProcessor proc = new ChainingProcessor(false);
    ProcessorProofObject proof = proc.processDPP(p);
    assertFalse(proof.applicable());
  }

  @Test
  public void testOneRecDPSelfChaining() {
    TRS trs = makeTRSWithOneRecDP();
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    assertEquals(1, p.getDPList().size());
    ChainingProcessor proc = new ChainingProcessor(true);
    assertTrue(proc.isApplicable(p));
    ProcessorProofObject proof = proc.processDPP(p);
    assertTrue(proof.applicable());
    List<Problem> results = proof.queryResults();
    assertEquals(1, results.size());
    Problem q = results.getFirst();
    List<DP> qDPs = q.getDPList();
    assertEquals(1, qDPs.size());
    DP qDP = q.getDPList().getFirst();
    assertEquals(qDP.lhs().queryRoot(), qDP.rhs().queryRoot());
  }

  @Test
  public void testTwoNonRecDPSelfChaining() {
    TRS trs = makeTRSWithTwoDPsChain();
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    assertEquals(2, p.getDPList().size());
    ChainingProcessor proc = new ChainingProcessor(true);
    assertTrue(proc.isApplicable(p));
    ProcessorProofObject proof = proc.processDPP(p);
    assertTrue(proof.applicable());
    List<Problem> results = proof.queryResults();
    assertEquals(1, results.size());
    Problem q = results.getFirst();
    List<DP> qDPs = q.getDPList();
    assertEquals(1, qDPs.size());
    DP qDP = q.getDPList().getFirst();
    Term expectedRhsArg = CoraInputReader.readTerm("3*(y-1)", trs);
    Term actualRhsArg = qDP.rhs().queryArgument(2);
    assertTrue(expectedRhsArg.equalsModuloRenaming(actualRhsArg));
  }
}
