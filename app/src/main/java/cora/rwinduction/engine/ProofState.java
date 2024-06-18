package cora.rwinduction.engine;

import charlie.trs.Rule;

import java.util.List;

public class ProofState {
  private List<Equation> _equations;
  private List<Rule> _hypotheses;

  public ProofState(List<Equation> initialEquations) {
    if (initialEquations == null)
      throw new IllegalArgumentException("initialEquations cannot be null");

    _equations = initialEquations;
  }

  public List<Equation> getEquations() {
    return _equations;
  }

  public List<Rule> getHypotheses() {
    return _hypotheses;
  }

  public void deleteEquation(int index) {
    _equations.remove(index);
  }

  public void addHypothese(Rule rule) {
    _hypotheses.add(rule);
  }

}
