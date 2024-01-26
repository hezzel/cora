package cora.termination.dependency_pairs.processors;

import cora.smt.SmtProblem;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;
import cora.terms.FunctionSymbol;
import cora.terms.Term;

import java.util.ArrayList;
import java.util.List;

public class SubtermProcessor implements Processor {

  private SmtProblem _smt;

  @Override
  public boolean isApplicable(Problem dp) {
    return true;
  }

  private static void generateFnConstraints(Problem dpp){
    List<FunctionSymbol> sharps = new ArrayList<>();
    Term s;
  }


  @Override
  public List<Problem> processDPP(Problem dpp) {
    return null;
  }
}
