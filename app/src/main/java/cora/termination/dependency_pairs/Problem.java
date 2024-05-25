package cora.termination.dependency_pairs;

import cora.data.digraph.Digraph;
import charlie.exceptions.IndexingError;
import charlie.exceptions.NullInitialisationError;
import charlie.trs.TRS;
import charlie.terms.FunctionSymbol;
import charlie.types.Type;
import charlie.types.TypeFactory;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

public class Problem {
  private final List<DP> _dps;
  private Digraph _graph;
  private TRS _trs;

  public Problem (@NotNull List<DP> dps, @NotNull TRS trs, @NotNull Digraph graph) {
    if (dps == null || trs == null || graph == null) {
      throw new NullInitialisationError(
        "Problem",
        "one of the arguments"
      );
    }

    if (dps.size() == graph.getNumberOfVertices()) {
      _dps = dps;
      _graph = graph;
      _trs = trs;
    } else {
      throw new IllegalArgumentException ("Error initializing new DP problem.\n" +
        "The number of DPs in the problem is " + dps.size() + " while their graph has " +
        graph.getNumberOfVertices() + " vertices"
      );
    }
  }

  public Problem(@NotNull List<DP> dps, @NotNull TRS trs) {
    if (dps == null) throw new NullInitialisationError (
      "Problem",
      "trying to create a DP problem with null reference dps."
    );
    _dps = dps;
    _trs = trs;
  }

  public List<DP> getDPList() {
    return _dps;
  }

  public Optional<Digraph> getGraph() {
    return Optional.ofNullable(_graph);
  }

  public TRS getTRS() {
    return _trs;
  }

  public Set<FunctionSymbol> getSharpHeads() {
    Set<FunctionSymbol> allFns = new TreeSet<>();
    Type dpSort = TypeFactory.createSort("DP_SORT");

    for (DP dp : _dps) {
      dp.lhs().storeFunctionSymbols(allFns);
      dp.rhs().storeFunctionSymbols(allFns);
    }

    return allFns
      .stream()
      .filter(f -> f.queryType().queryOutputType().equals(dpSort))
      .collect(Collectors.toSet());
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    for (int i = 0; i < _dps.size(); i++) {
      builder.append("  ");
      builder.append(_dps.get(i).toString());
      builder.append("\n");
    }
    return builder.toString();
  }
}
