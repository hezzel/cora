/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine.deduction;

import java.util.ArrayList;
import java.util.Optional;
import charlie.terms.position.Position;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TermFactory;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This deduction step handles the "generalise subterm <term>" command syntax, which replaces all
 * occurrences of a given subterm by a variable.  We only consider subterms at full positions, not
 * partial positions.
 */
public final class DeductionGeneraliseSubterm extends DeductionStep {
  private Term _replaced;
  private Variable _replacement;
  private Renaming _renaming;
  private Equation _newEquation;

  private DeductionGeneraliseSubterm(ProofState state, ProofContext context,
                                     Term replaced, Variable replacement, Renaming renaming,
                                     Term newLeft, Term newRight, Term newConstr) {
    super(state, context);
    _replaced = replaced;
    _replacement = replacement;
    _renaming = renaming;
    _newEquation = new Equation(newLeft, newRight, newConstr);
  }

  /**
   * This creates the step replacing the given subterm by a fresh variable with the given name.
   * The name is allowed to be null, but not a name that already occurs in the equation context.
   * This will fail if the subterm does not occur in the left-hand side, right-hand side or
   * constraint of the top equation (the decution step is not meant to generalise the bounding
   * terms).
   */
  public static DeductionGeneraliseSubterm createStep(PartialProof proof,
                                                      Optional<OutputModule> module,
                                                      Term subterm,
                                                      String newvarname) {
    ProofState state = proof.getProofState();
    ProofContext context = proof.getContext();
    Equation eq = getTopEquation(state, module);
    if (eq == null) return null;

    ArrayList<Position> leftPosses = getSubtermPositions(eq.getLhs(), subterm);
    ArrayList<Position> rightPosses = getSubtermPositions(eq.getRhs(), subterm);
    ArrayList<Position> constrPosses = getSubtermPositions(eq.getConstraint(), subterm);
    
    if (leftPosses.isEmpty() && rightPosses.isEmpty() && constrPosses.isEmpty()) {
      module.ifPresent(o -> o.println("No such subterm in the equation: %a",
        Printer.makePrintable(subterm, state.getTopEquation().getRenaming())));
      return null;
    }

    VariableNamer.VariableInfo info = context.getVariableNamer().getVariableInfo(newvarname);
    Variable x = TermFactory.createVar(info.basename(), subterm.queryType());
    MutableRenaming renaming = state.getTopEquation().getRenaming().copy();
    if (!renaming.setName(x, newvarname)) {
      if (renaming.getReplaceable(newvarname) != null) {
        module.ifPresent(o -> o.println("The variable name %a is not fresh.", newvarname));
      }
      else {
        module.ifPresent(o -> o.println("The name %a is not a legal variable name.", newvarname));
      }
      return null;
    }

    Term left = replacePositions(eq.getLhs(), leftPosses, x);
    Term right = replacePositions(eq.getRhs(), rightPosses, x);
    Term cstr = replacePositions(eq.getConstraint(), constrPosses, x);

    return new DeductionGeneraliseSubterm(state, context, subterm, x, renaming, left, right, cstr);
  }

  /** Returns all full positions in term where subterm occurs. */
  private static ArrayList<Position> getSubtermPositions(Term term, Term subterm) {
    ArrayList<Position> ret = new ArrayList<Position>();
    term.visitSubterms( (s,p) -> { if (s.equals(subterm)) ret.add(p); });
    return ret;
  }

  /**
   * Given a set of parallel positions in term, this replaces the subterm at each of these
   * positions by replacement.  We assume that replacement has the right type to do so.
   */
  private static Term replacePositions(Term term, ArrayList<Position> posses, Term replacement) {
    for (Position pos : posses) term = term.replaceSubterm(pos, replacement);
    return term;
  }

  /** There's nothing to check; we can always generalise in this way. */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    return true;
  }

  /**
   * When making the new equation context, we make the following considerations on what to do with
   * the bounding term a when before we had a ≽ A | φ:
   * - if a was ⊤, then we keep ⊤
   * - if a and A and the constraint do not have the replacement as a subterm, then we keep a
   * - otherwise we choose A as a guaranteed-safe bounding term
   */
  private EquationContext makeNewEquationContext() {
    EquationContext old = _state.getTopEquation();
    Optional<Term> leftGreater = old.getLeftGreaterTerm();
    if (!leftGreater.isEmpty()) {
      if (old.getEquation().getLhs() != _newEquation.getLhs() ||
          old.getEquation().getConstraint() != _newEquation.getConstraint() ||
          !getSubtermPositions(leftGreater.get(), _replaced).isEmpty()) {
        leftGreater = Optional.of(_newEquation.getLhs());
      }
    }
    Optional<Term> rightGreater = old.getRightGreaterTerm();
    if (!rightGreater.isEmpty()) {
      if (old.getEquation().getRhs() != _newEquation.getRhs() ||
          old.getEquation().getConstraint() != _newEquation.getConstraint() ||
          !getSubtermPositions(rightGreater.get(), _replaced).isEmpty()) {
        rightGreater = Optional.of(_newEquation.getRhs());
      }
    }
    return new EquationContext(leftGreater, _newEquation, rightGreater,
                               _state.getLastUsedIndex()+1, _renaming);
  }

  /**
   * In applying the generalisation, we particularly have to take care that we set the bounding
   * terms correctly: if a side has changed and the bounding term on that side was not TOP, we set
   * the bounding term to the term itself, to be certain that the conditions of a bounded equation
   * context are still satisfied.
   */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    EquationContext ec = makeNewEquationContext();
    return _state.replaceTopEquation(ec).setIncomplete(ec.getIndex());
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("generalise subterm ");
    printer.add(printer.makePrintable(_replaced, _renaming));
    printer.add(" as ", _renaming.getName(_replacement));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply GENERALISE to replace the equation context %a by %a.",
      _equ.getName(), makeNewEquationContext());
  }
}

