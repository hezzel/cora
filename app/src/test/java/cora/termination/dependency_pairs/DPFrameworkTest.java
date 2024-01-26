package cora.termination.dependency_pairs;

import cora.parsing.CoraInputReader;
import cora.rewriting.TRS;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class DPFrameworkTest {

  @Test
  void testProveTermination() {
    String program =
      "sum :: Int -> Int\n" +
        "f :: int -> Int\n" +
        "z :: int\n" +
      "sum(x) -> 0         | x ≤ 0\n" +
      "sum(x) -> x + sum(x - 1) | x > 0\n" +
        "sum(x) -> f(z)\n" +
        "f(x) -> 0";
    TRS trs = CoraInputReader.readProgramFromString(program);

    System.out.println("Input TRS: " + trs);

    System.out.println("Ignoring the constraints for now...");



  }
}
