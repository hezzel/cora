package cora.rwinduction.engine;

import charlie.exceptions.NullStorageException;
import charlie.trs.Rule;
import com.google.common.collect.ImmutableList;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

/**
 * TODO explain proof states.
 */
class ProofState {
  private final ImmutableList<Equation> _equations;
  private final ImmutableList<Rule> _hypotheses;

  public ProofState(@NotNull ImmutableList<Equation> initialEquations) {
    if (initialEquations == null)
      throw new NullStorageException("ProofState", "initialEquations cannot be null");

    _equations = initialEquations;
    _hypotheses = ImmutableList.of();
  }

  /**
   * Builds a new proof state of the form (E, empty).
   */
  private ProofState(@NotNull ImmutableList<Equation> equations,
                     @NotNull ImmutableList<Rule> hypotheses) {
    _equations = equations;
    _hypotheses = hypotheses;
  }

  /**
   * Returns the list of equations in this proof state.
   */
  public ImmutableList<Equation> getEquations() {
    return _equations;
  }

  /**
   * Returns the list of hypotheses in this proof state.
   */
  public ImmutableList<Rule> getHypotheses() {
    return _hypotheses;
  }

  /**
   * This given a proof state {@code (E, H)} and an equation {@code equation},
   * this method returns the new proof state in which {@code equation} is added to E.
   * The hypotheses in H are unaltered.
   * @param equation the new equation
   * @return the new proof state
   */
  public ProofState addEquation(Equation equation) {
    return new ProofState(
      ImmutableList.<Equation>builder()
        .addAll(_equations)
        .add(equation)
        .build(),
      _hypotheses
    );
  }

  /**
   * Given a proof state {@code (E, H)} this method returns a new proof state in which the
   * equation at index {@code equationIndex} is removed.
   * The rules on {@code H} remains unaltered.
   * @param equationIndex the index of an equation in E
   * @return the new proof state
   * @throws IndexOutOfBoundsException if the equationIndex is out of range
   *         ({@code equationIndex < 0 || equationIndex >= E.size()})
   */
  public ProofState deleteEquation(int equationIndex) {
    ImmutableList.Builder<Equation> builder = ImmutableList.builder();

    for(int i = 0 ; i < _equations.size() ; i++) {
      if (i != equationIndex)
        builder.add(_equations.get(i));
    }

    ImmutableList<Equation> equations = builder.build();

    return new ProofState(equations, _hypotheses);
  }

  public ProofState addHypothesis(Rule rule) {
    return new ProofState(
      _equations,
      ImmutableList.<Rule>builder()
        .addAll(_hypotheses)
        .add(rule)
        .build()
    );
  }


  @Contract(" -> new")
  static @NotNull ProofState createEmptyState() {
    return new ProofState(ImmutableList.of());
  }

}
