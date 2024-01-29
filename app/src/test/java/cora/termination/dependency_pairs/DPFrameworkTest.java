package cora.termination.dependency_pairs;

import cora.reader.CoraInputReader;
import cora.rewriting.TRS;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class DPFrameworkTest {

  @Test
  void testProveTermination() {
    String program =
      "rec :: (Int -> Int -> Int) -> Int -> Int -> Int\n" +
        "rec(F, x, y) -> y | x ≤ 0\n" +
        "rec(F, x, y) -> F(x, rec(F, x-1, y)) | x > 0\n" +
        "\n" +
        "readint :: Int\n" +
        "readint → y\n" +
        "\n" +
        "myfun :: Int -> Int -> Int\n" +
        "myfun(x, z) -> x + z";

    TRS trs = CoraInputReader.readTrsFromString(program);

    System.out.println("Input TRS: " + trs);

    DPFramework dp = new DPFramework();

    dp.proveTermination(trs);



  }
}
