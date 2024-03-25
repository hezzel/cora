package cora.termination.dependency_pairs.processors;

import cora.reader.CoraInputReader;
import cora.trs.TRS;
import cora.trs.TrsFactory;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

class SubtermProcessorTest {
  private static boolean ENABLE = false;

  @Test
  void testSubcritWithAckermann() {
    TRS trs = CoraInputReader.readTrsFromString(
      "s :: Nat -> Nat\n" +
      "0 :: Nat\n" +
      "ack :: Nat -> Nat -> Nat\n" +
      "ack(0, n) -> s(n)\n" +
      "ack(s(m),0) -> ack(m, s(0))\n" +
      "ack(s(m),s(n)) -> ack(m, ack(s(m),n))\n",
      TrsFactory.MSTRS);

    Problem p = DPGenerator.generateProblemFromTrs(trs);

    SubtermProcessor subProc = new SubtermProcessor();
    // TODO: do an assert with the output of this
    if (ENABLE) subProc.processDPP(p);
  }

  @Test
  void testSubcritWithMutuallyRecursiveFunctions() {
    TRS trs = CoraInputReader.readTrsFromString(
      "s :: Nat -> Nat\n" +
      "o :: Nat\n" +
      "f :: Nat -> Nat -> Nat\n" +
      "f(s(x), y) -> g(y, x, 3)\n" +
      "g :: Nat -> Nat -> Int -> Nat\n" +
      "g(x, y, i) -> f(y, x) | i <= 0\n" +
      "g(x, y, i) -> g(s(x), y, i-1) | i > 0\n");
    SubtermProcessor subProc = new SubtermProcessor();
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    // TODO: do an assert with the output of this
    if (ENABLE) subProc.processDPP(p);
  }

  @Test
  public void testSubcritNotApplicable() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x, y) -> f(x, y+1) | y < x\n");
    SubtermProcessor subProc = new SubtermProcessor();
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    // TODO: do an assert with the output of this
    if (ENABLE) assertFalse(subProc.processDPP(p).applicable());
  }
}
