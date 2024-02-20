package cora.termination.dependency_pairs;

import cora.reader.CoraInputReader;
import cora.trs.TRS;
import cora.termination.Handler;
import cora.termination.dependency_pairs.certification.Informal;
import cora.utils.Pair;
import org.junit.jupiter.api.Test;

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

    System.out.println(Informal.getInstance().getInformalProof());
*/
  }
}
