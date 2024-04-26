package cora.termination.dependency_pairs.processors;

import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.solvesmt.ExternalSmtSolver;
import cora.config.Settings;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class KasperProcessorTest {

  @Test
  void processDPP() {
    Settings.smtSolver = new ExternalSmtSolver();

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
