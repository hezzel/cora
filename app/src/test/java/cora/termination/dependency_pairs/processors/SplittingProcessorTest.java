package cora.termination.dependency_pairs.processors;

import cora.reader.CoraInputReader;
import cora.rewriting.TRS;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.DP;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

class SplittingProcessorTest {
  @Test
  void testNothingToSplit() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x, y) -> f(x, y-1) | x < y ∧ (1 = 2 ∧ x < y + 1)"
    );

    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    assertTrue(splitProc.processDPP(p).isEmpty());
  }

  @Test
  public void testObviousSplitNeq() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x ,y) -> f(x, y-1) | x != y");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    Optional<List<Problem>> result = splitProc.processDPP(p);
    assertFalse(result.isEmpty());
    assertTrue(result.get().size() == 1);
    assertTrue(result.get().get(0).toString().equals(
      "[f#(x, y) -> f#(x, y - 1) [ x > y ] , f#(x, y) -> f#(x, y - 1) [ x < y ] ]"));
  }

  @Test
  public void testObviousSplitOr() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x ,y) -> f(x, y-1) | x = 1 ∨ x = 3 ∨ x = 10");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    Optional<List<Problem>> result = splitProc.processDPP(p);
    assertFalse(result.isEmpty());
    assertTrue(result.get().size() == 1);
    assertTrue(result.get().get(0).toString().equals(
      "[f#(x, y) -> f#(x, y - 1) [ x = 1 ] , f#(x, y) -> f#(x, y - 1) [ x = 3 ] , " +
      "f#(x, y) -> f#(x, y - 1) [ x = 10 ] ]"));
  }

  @Test
  public void testNeqAtStartOfConstraint() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x, y) -> f(x, y-1) | x != y ∧ x ≤ y");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    Optional<List<Problem>> result = splitProc.processDPP(p);
    assertFalse(result.isEmpty());
    assertTrue(result.get().size() == 1);
    assertTrue(result.get().get(0).toString().equals(
      "[f#(x, y) -> f#(x, y - 1) [ x > y ∧ x ≤ y ] , " +
       "f#(x, y) -> f#(x, y - 1) [ x < y ∧ x ≤ y ] ]"));
  }

  @Test
  public void testOrInMiddleOfConstraint() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "g :: Int -> Int\n" +
      "h :: Int -> Int\n" +
      "f(x) -> f(x+1) | 3 = 4 ∧ (x < 0 ∨ x > 10)" +
      "g(x) -> f(x) | x <= 0");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    Optional<List<Problem>> result = splitProc.processDPP(p);
    assertFalse(result.isEmpty());
    assertTrue(result.get().size() == 1);
    assertTrue(result.get().get(0).toString().equals(
      "[f#(x) -> f#(x + 1) [ 3 = 4 ∧ x < 0 ] , f#(x) -> f#(x + 1) [ 3 = 4 ∧ x > 10 ] , " +
       "g#(x) -> f#(x) [ x ≤ 0 ] ]"));
  }

  @Test
  public void testTwoSplittables() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x,y) -> f(x+2,y-1) | x != y ∧ y > 0 ∧ (x % 2 = 0 ∨ x % 3 != 0)");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    Optional<List<Problem>> result = splitProc.processDPP(p);
    assertFalse(result.isEmpty());
    assertTrue(result.get().size() == 1);
    List<DP> lst = result.get().get(0).getDPList();
    assertTrue(lst.size() == 4);
    assertTrue(lst.get(0).constraint().toString().equals("x > y ∧ y > 0 ∧ x % 2 = 0"));
    assertTrue(lst.get(1).constraint().toString().equals("x < y ∧ y > 0 ∧ x % 2 = 0"));
    assertTrue(lst.get(2).constraint().toString().equals("x > y ∧ y > 0 ∧ x % 3 ≠ 0"));
    assertTrue(lst.get(3).constraint().toString().equals("x < y ∧ y > 0 ∧ x % 3 ≠ 0"));
  }

  @Test
  public void testTripleSplittables() {
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "f(x,y) -> f(x+2,y-1) | x != y ∧ y != 0 ∧ (x % 2 = 0 ∨ x % 3 != 0)");
    Problem p = DPGenerator.generateProblemFromTrs(trs);
    SplittingProcessor splitProc = new SplittingProcessor();
    assertTrue(splitProc.processDPP(p).isEmpty());
  }
}
