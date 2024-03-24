package cora.termination.dependency_pairs;

import org.junit.jupiter.api.Test;

import cora.reader.CoraInputReader;
import charlie.trs.TRS;
import cora.termination.TerminationHandler;

import java.util.Optional;

class DPFrameworkTest {

  @Test
  void testProveTermination() {
    String program =
      "eval :: Int -> Int -> Int\n" +
      "eval(x, y) -> eval(x - 1, y) | x>y";

    TRS trs = CoraInputReader.readTrsFromString(program);

    DPFramework dp = new DPFramework();
/*
    Pair<Handler.Answer, Optional<String>> proof = dp.proveTermination(trs);

    System.out.println(proof.fst());
*/
  }
}
