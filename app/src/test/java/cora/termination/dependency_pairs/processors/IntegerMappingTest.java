package cora.termination.dependency_pairs.processors;

import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import charlie.solvesmt.ProcessSmtSolver;
import cora.config.Settings;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class IntegerMappingTest {

  // @Test
  // TODO
  void processDPP() {
    Settings.smtSolver = new ProcessSmtSolver();

    // This is the TRS that fails and shouldn't
    TRS trs = CoraInputReader.readTrsFromString(
      "sum :: Int -> Int \n" +
      "sum(x) -> sum(x - 1) | x > 0"
    );

    Problem p = (new DPGenerator(trs)).queryProblem(false, false);

    // Let's get SCCS for it...
    IntegerMappingProcessor imapProc = new IntegerMappingProcessor();
    imapProc.processDPP(p);
  }
}
