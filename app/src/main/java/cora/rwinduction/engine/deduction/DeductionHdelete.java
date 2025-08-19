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

import java.util.Optional;
import charlie.util.Pair;
import charlie.terms.position.Position;
import charlie.terms.position.ArgumentPos;
import charlie.terms.position.FinalPos;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * The deduction command for removing a goal that's a contextualised instance of an induction
 * hypothesis.
 *
 * In theory, the hdelete deduction rule may add a requirement s ≻ l γ or t ≻ r γ.  However, in
 * practice we ensure that this is satisfied exactly if s != l γ or t != r γ, so we always either
 * don't allow the deduction rule to be applied at all, or allow it without further constraints.
 */
public final class DeductionHdelete extends DeductionStep {
  private ConstrainedReductionHelper _helper;
  private String _hypothesisName;
  private boolean _inversed;

  /** Private constructor, called (only) by createStep */
  private DeductionHdelete(ProofState state, ProofContext context, String hypoName,
                            boolean inverse, ConstrainedReductionHelper h) {
    super(state, context);
    _helper = h;
    _hypothesisName = hypoName;
    _inversed = inverse;
  }

  /**
   * Creates an hdelete step for the given information, checking that there is indeed a match but
   * NOT that the constraint is satisfied.
   * The substitution will not be altered, and does not become the property of the step; it is
   * safe to change afterwards.
   * If an ordering requirement must be imposed, it will be done at the side where the equation
   * context is applied, unless either this side would yield an unsolvable requirement, or choosing
   * the other side would yield no requirement at all.
   */
  public static DeductionHdelete createStep(PartialProof proof, Optional<OutputModule> m,
                                            Hypothesis hypo, boolean inverse,
                                            EquationPosition pos, Substitution subst) {
    ConstrainedReductionHelper helper = setupHelper(hypo, inverse, proof, pos, subst);
    EquationContext original = proof.getProofState().getTopEquation();
    if (!helper.extendSubstitutionBasic(m)) return null;
    if (!helper.extendSubstitutionRight(m)) return null;
    helper.extendSubstitutionWithConstraintDefinitions();
    Position p = pos.queryPosition();
    if (!sameContexts(original.getEquation(), p)) {
      m.ifPresent(o -> printBadContextError(original, p, o));
      return null;
    }
    if (!resultingOrderingRequirementOK(original, p, m)) return null;

    return new DeductionHdelete(proof.getProofState(), proof.getContext(),
                                hypo.getName() + (inverse ? "^{-1}" : ""), inverse, helper);
  }

  /**
   * Helper function for createStep: this sets up the constrained reduction helper for the given
   * hypothesis (and direction).
   */
  private static ConstrainedReductionHelper setupHelper(Hypothesis hypo, boolean inverse,
                                    PartialProof proof, EquationPosition pos, Substitution subst) {
    Equation hequ = hypo.getEquation();
    Term left = inverse ? hequ.getRhs() : hequ.getLhs();
    Term right = inverse ? hequ.getLhs() : hequ.getRhs();
    return new ConstrainedReductionHelper(left, right, hequ.getConstraint(), hypo.getRenamingCopy(),
                                          "induction hypothesis", proof, pos, subst);
  }

  /**
   * This returns whether the left-hand side and right-hand side of the given equation have the same
   * context around position pos.
   */
  private static boolean sameContexts(Equation equation, Position pos) {
    Term left = equation.getLhs();
    Term right = equation.getRhs();
    while (pos instanceof ArgumentPos p) {
      if (!left.isApplication() || !right.isApplication() ||
          left.numberArguments() != right.numberArguments() ||
          !left.queryHead().equals(right.queryHead())) return false;
      int index = p.queryHead();
      for (int i = 1; i <= left.numberArguments(); i++) {
        if (i != index && !left.queryArgument(i).equals(right.queryArgument(i))) return false;
      }
      left = left.queryArgument(index);
      right = right.queryArgument(index);
      pos = p.queryTail();
    }
    if (pos.isEmpty()) return true;
    if (pos instanceof FinalPos f) {
      if (!left.isApplication() || !right.isApplication()) return false;
      int chop = f.queryChopCount();
      if (left.numberArguments() < chop || right.numberArguments() < chop) return false;
      for (int i = 0; i < chop; i++) {
        if (!left.queryArgument(left.numberArguments()-i).equals(
              right.queryArgument(right.numberArguments()-i))) return false;
      }
      return true;
    }
    else {
      throw new IllegalArgumentException("Positions may only be argument or final positions.");
    }
  }

  /**
   * Prints an error explaining that the two sides of the equation are not the same context to o.
   * Note that it is given that both sides of the equation do have the given position, and the terms
   * at these positions have the same type.
   */
  private static void printBadContextError(EquationContext ec, Position pos, OutputModule o) {
    Term left = ec.getEquation().getLhs();
    Term right = ec.getEquation().getRhs();
    MutableRenaming renaming = ec.getRenamingCopy();
    Term subterm = left.querySubterm(pos);
    Variable x = TermFactory.createVar("[]", subterm.queryType());
    left = left.replaceSubterm(pos, x);
    right = right.replaceSubterm(pos, x);
    // try to give it a good name, but if that fails, just print it in whatever funky way the
    // output module decides to handle a variable that has no name
    if (!renaming.setName(x, "[]") && !renaming.setName(x, "[ ]") &&
        !renaming.setName(x, "BOX") && !renaming.setName(x, "#")) renaming.setName(x, "CONTEXT");
    o.println("The two sides have different contexts: %a versus %a.",
      Printer.makePrintable(left, renaming), Printer.makePrintable(right, renaming));
  }

  /**
   * This checks if the ordering requirements to apply the hdelete step at the given position are
   * automatically satisfied.  If so, true is returned.  If not, false is returned and a message
   * is printed on the output module.
   */
  private static boolean resultingOrderingRequirementOK(EquationContext original,
                                                        Position pos,
                                                        Optional<OutputModule> m) {
    if (original.getLeftGreaterTerm().isEmpty() ||
        original.getRightGreaterTerm().isEmpty() ||
        !pos.isEmpty()) return true;
    if (!original.getLeftGreaterTerm().get().equals(original.getEquation().getLhs()) ||
        !original.getRightGreaterTerm().get().equals(original.getEquation().getRhs())) return true;
    m.ifPresent(o -> o.println("Cannot apply an induction hypothesis at position %a when both " +
      "bounding terms are the same as the equation terms.", pos));
    return false;
  }

  /**
   * This function checks if we can indeed apply the induction hypothesis in the direction l → r | φ
   * with the substitution γ to the equation C[lγ]_p ≈ C[rγ]_p | ψ, with data as given by step.
   * Note that, for a step to be created, it is already given that l γ and r γ are indeed the
   * subterms at the given position of the equation, and the surrounding context is the same.
   * Hence, the remaining checks are:
   * - check that all (meta-)vars in the rule are in dom(δ)
   * - check that ψ ⇒ φδ is valid
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    if (_helper.constraintIsTrue()) return true;
    return _helper.checkConstraintGoodForReduction(module, Settings.smtSolver);
  }

  @Override
  protected ProofState tryApply(Optional<OutputModule> module) {
    return _state.deleteTopEquation();
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("hdelete ", _hypothesisName, " ", _helper.queryPosition(), " with ",
      _helper.substitutionPrintable(_equ.getRenamingCopy()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply HDELETE to %a with induction hypothesis %a and substitution %a.",
      _equ.getName(), _hypothesisName, _helper.substitutionPrintable(_equ.getRenamingCopy()));
  }
}

