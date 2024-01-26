package cora.termination.dependency_pairs;

import cora.rewriting.TRS;
import cora.termination.Prover.Answer;
import cora.termination.dependency_pairs.processors.GraphProcessor;

import java.util.List;

import static cora.termination.Prover.Answer.MAYBE;
import static cora.termination.Prover.Answer.NO;

public class DPFramework {

  private static Boolean isTRSApplicable() {
    return true;
  }

  private static Problem computeInitialProblem(TRS trs) {
    return DPGenerator.generateProblemFromTrs(trs);
  }

  public static Answer proveTermination(TRS trs) {
    GraphProcessor graphProcesor = new GraphProcessor();
    Problem initialProblem = DPFramework.computeInitialProblem(trs);
    List<Problem> dpsFromGraph = graphProcesor.processDPP(initialProblem);

    System.out.println("New problems that came from the GraphProcessor: \n" + dpsFromGraph);

//    System.out.println("\nCannot find Kasper's processor.\nMAYBE");


    return MAYBE;
  }

}
