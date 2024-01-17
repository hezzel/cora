package cora.termination.dependency_pairs;

import cora.data.digraph.Digraph;
import cora.exceptions.NullInitialisationError;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public class Problem {
  private List<DP> _dps;
  private Digraph _graph;

  public Problem(@NotNull List<DP> dps) {
    if (dps == null) throw new NullInitialisationError(
      "Problem",
      "trying to create a DP problem with null reference dps."
    );
    _dps = dps;
  }

  public Problem (@NotNull List<DP> dps, @NotNull Digraph graph) {
    if (dps == null || graph == null) throw new NullInitialisationError (
      "Problem",
      // update this message to a proper one
      "for god's sake don't create objects with null arguments!"
    );
    _dps = dps;
    _graph = graph;
  }

  public List<DP> getProblem() {
    return _dps;
  }

  public Optional<Digraph> getGraph() {
    return Optional.ofNullable(_graph);
  }

  @Override
  public String toString() {
    return _dps.toString();
  }

}
