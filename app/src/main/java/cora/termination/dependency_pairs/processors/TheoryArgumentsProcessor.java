package cora.termination.dependency_pairs.processors;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.TreeMap;
import cora.types.Type;
import cora.terms.FunctionSymbol;
import cora.termination.dependency_pairs.Problem;

public class TheoryArgumentsProcessor implements Processor {
  private TreeMap<FunctionSymbol,Set<Integer>> _targs;

  public boolean isApplicable(Problem dpp) {
    return true;
  }

  /**
   * Sets up _targs to map each f in Heads(dpp) to the set of all argument positions of theory
   * sort.
   */
  private void setupInitialArgumentsFunction(Problem dpp) {
    _targs = new TreeMap<FunctionSymbol,Set<Integer>>();
    Set<FunctionSymbol> allFns = dpp.getSharpHeads();
    for (FunctionSymbol f : allFns) {
      _targs.put(f, new TreeSet<Integer>());
      Type t = f.queryType();
      for (int i = 1; t.isArrowType(); i++, t = t.subtype(2)) {
        Type argtype = t.subtype(1);
        if (t.isBaseType() && t.isTheoryType()) _targs.get(f).add(i);
      }
    }
    System.out.println(_targs);
  }

  public Problem transform(Problem dpp) {
    return dpp;
  }

  public Optional<List<Problem>> processDPP(Problem dpp) {
    setupInitialArgumentsFunction(dpp);
    return Optional.empty();
  }
}
