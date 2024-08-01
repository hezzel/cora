package cora.rwinduction.engine.data;

import charlie.exceptions.NullStorageException;
import charlie.trs.Rule;
import charlie.trs.TRS;
import com.google.common.collect.ImmutableList;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

/** TODO document this method
 * @apiNote All methods provided by this class are immutable.
 * For instance, {@link ProofState#addEquation(Equation)} does not modify the current object but
 * returns a new proof state with the new equation instead.
 */
public class ProofState {
  private final TRS _trs;
  private final ImmutableList<Equation> _equations;
  private final ImmutableList<Rule> _hypotheses;

  /**
   * Instantiates a new proof state object with the following data:
   * @param trs the TRS used in the rewriting induction mechanism, note that {@code ProofState}
   *           objects do not provide methods to change this TRS.
   *            All subsequent changes on the proof state by the deduction rules use the same
   *            initial TRS.
   * @param initialEquations the list of equations to be proved.
   */
  public ProofState(@NotNull TRS trs, @NotNull ImmutableList<Equation> initialEquations) {
    if (initialEquations == null)
      throw new NullStorageException("ProofState", "initialEquations cannot be null");

    if (trs == null)
      throw new NullStorageException("ProofState", "trs cannot be null");

    if (initialEquations == null)
      throw new NullStorageException("ProofState", "initialEquations cannot be null");

    _trs = trs;
    _equations = initialEquations;
    _hypotheses = ImmutableList.of();
  }

  /**
   *
   */
  private ProofState(@NotNull TRS trs,
                     @NotNull ImmutableList<Equation> equations,
                     @NotNull ImmutableList<Rule> hypotheses) {
    _trs = trs;
    _equations = equations;
    _hypotheses = hypotheses;
  }

  public TRS getTRS() {
    return _trs;
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
  @Contract(pure = true)
  public ProofState addEquation(Equation equation) {
    return new ProofState(
      _trs,
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
  @Contract(pure = true)
  public ProofState deleteEquation(int equationIndex) {
    ImmutableList.Builder<Equation> builder = ImmutableList.builder();

    for(int i = 0 ; i < _equations.size() ; i++) {
      if (i != equationIndex)
        builder.add(_equations.get(i));
    }

    ImmutableList<Equation> equations = builder.build();

    return new ProofState(_trs, equations, _hypotheses);
  }

  /**
   *
   * @param equationIndex
   * @param equation
   * @return
   */
  @Contract(pure = true)
  public ProofState replaceEquation(int equationIndex, Equation equation) {
    ImmutableList.Builder<Equation> builder = ImmutableList.builder();
    for(int i = 0 ; i < _equations.size() ; i++) {
      if (i != equationIndex) {
        builder.add(_equations.get(i));
      } else {
        builder.add(equation);
      }
    }
    ImmutableList<Equation> equations = builder.build();

    return new ProofState(_trs, equations, _hypotheses);
  }

  @Contract(pure = true)
  public ProofState addHypothesis(Rule rule) {
    return new ProofState(
      _trs,
      _equations,
      ImmutableList.<Rule>builder()
        .addAll(_hypotheses)
        .add(rule)
        .build()
    );
  }

  /**
   * Returns whether this state is a final state, that is, the set of equations, i.e.,
   * the proof goal, is empty.
   */
  public boolean isFinalState() {
    return _equations.isEmpty();
  }

  @Contract(" -> new")
  public static @NotNull ProofState createInitialState(TRS trs, ImmutableList<Equation> equations) {
    return new ProofState(trs, equations);
  }

}
