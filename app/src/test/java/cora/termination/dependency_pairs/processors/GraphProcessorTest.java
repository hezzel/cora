package cora.termination.dependency_pairs.processors;

import charlie.types.TypeFactory;
import cora.terms.Term;
import cora.terms.TermFactory;
import cora.reader.CoraInputReader;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

class GraphProcessorTest {

  @Test
  void processTest() {
    //System.out.println("We are considering the following TRS: ");
    String program =
      " a :: sort \n b :: sort \n c :: sort \n d :: sort \n" +
      " a -> a \n a -> b \n b -> c \n c -> b";

    //System.out.println(program);

    Problem dpp = DPGenerator.generateProblemFromTrs(CoraInputReader.readTrsFromString(program));

    //System.out.println("The DPP problem generated from this TRS is: " + dpp);

    GraphProcessor proc = new GraphProcessor();
    // TODO

  }

  @Test
  void isApplicable() {
  }

  @Test
  void processDPP() {
  }
}
