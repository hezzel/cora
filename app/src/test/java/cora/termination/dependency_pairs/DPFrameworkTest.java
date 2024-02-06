package cora.termination.dependency_pairs;

import cora.reader.CoraInputReader;
import cora.rewriting.TRS;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

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
      "F :: Int -> (Int -> Int) -> Int -> Int -> Int\n" +
        "G :: Int -> (Int -> Int) -> Int -> Int -> Int\n" +
        "\n" +
        "F(x, f, y, z) -> F(f(x), f, y-1, z) | x=y /\\ y>=z+1\n" +
        "G(x, f, y, z) -> G(x, f, F(x, f, y, z), z) | x>2 /\\ y>=x /\\ z+x>=0";

    TRS trs = CoraInputReader.readTrsFromString(program);

    System.out.println("Input TRS: " + trs);

    DPFramework dp = new DPFramework();

    dp.proveTermination(trs);



  }
}
