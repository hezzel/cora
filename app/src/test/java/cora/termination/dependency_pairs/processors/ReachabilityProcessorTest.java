package cora.termination.dependency_pairs.processors;

import charlie.reader.CoraInputReader;
import charlie.trs.TRS;
import charlie.solvesmt.ProcessSmtSolver;
import cora.config.Settings;
import cora.termination.dependency_pairs.DPGenerator;
import cora.termination.dependency_pairs.Problem;
import charlie.terms.TheoryFactory;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ReachabilityProcessorTest {

  @Test
  void processDPP() {
    Settings.smtSolver = new ProcessSmtSolver();
    TRS program = CoraInputReader.readTrsFromString("nil :: intlist\n" +
      "cons :: Int -> intlist -> intlist\n" +
      "\n" +
      "init :: (Int -> Int) -> intlist -> intlist\n" +
      "init(f) -> map([+](fsum(f, 10)))\n" +
      "\n" +
      "map :: (Int -> Int) -> intlist -> intlist\n" +
      "map(F, nil) -> nil\n" +
      "map(F, cons(H, T)) -> cons(F(H), map(F, T))\n" +
      "\n" +
      "private fsum :: (Int -> Int) -> Int -> Int\n" +
      "fsum(F, 0) -> 0\n" +
      "fsum(F, N) -> F(N) + fsum(F, N-1) | N != 0");

    Problem p = DPGenerator.generateProblemFromTrs(program);
    SplittingProcessor split = new SplittingProcessor();
    TheoryArgumentsProcessor targ = new TheoryArgumentsProcessor();

    p = split.transform(p).queryOutput();
    p = targ.transform(p).queryOutput();

    ReachabilityProcessor r = new ReachabilityProcessor();

    r.transform(p);

  }
}
