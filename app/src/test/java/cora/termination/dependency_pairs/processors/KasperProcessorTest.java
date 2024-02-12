package cora.termination.dependency_pairs.processors;

import cora.reader.CoraInputReader;
import cora.rewriting.TRS;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class KasperProcessorTest {

  @Test
  void processDPP() {

    // This is the TRS that fails and shouldn't
    TRS trs = CoraInputReader.readTrsFromString(
      "sum :: Int -> Int \n" +
        "sum(x) -> sum(x - 1) | x > 0"
    );

    Problem p = DPGenerator.generateProblemFromTrs(trs);

    // Let's get SCCS for it...
    KasperProcessor kasperProc = new KasperProcessor();
    kasperProc.processDPP(p);
  }
}
