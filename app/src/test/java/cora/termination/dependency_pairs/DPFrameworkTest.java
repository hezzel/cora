package cora.termination.dependency_pairs;

import cora.reader.CoraInputReader;
import cora.rewriting.TRS;
import org.junit.jupiter.api.Test;

class DPFrameworkTest {

  @Test
  void testProveTermination() {
//    String program =
//        " Z :: nat \n" +
//        "S :: nat -> nat \n" +
//        "plus :: nat -> nat -> nat\n" +
//        "plus(x, Z) -> Z\n" +
//        "plus(x, S(y)) -> S(plus(x,y))";

    String program =
      "eval :: Int -> Int -> Int\n" +
        "\n" +
        "eval(x, y) -> eval(x-1, y) | x>0";

    TRS trs = CoraInputReader.readTrsFromString(program);

    AccessibilityChecker acc = new AccessibilityChecker(trs);
    System.out.println(acc.checkAccessibility());

//    System.out.println("Input TRS: " + trs);

    DPFramework dp = new DPFramework();
    dp.proveTermination(trs);

  }
}
