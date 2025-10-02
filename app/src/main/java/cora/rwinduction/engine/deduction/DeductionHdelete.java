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
import charlie.util.Pair;
import charlie.terms.position.Position;
import charlie.terms.position.ArgumentPos;
import charlie.terms.position.FinalPos;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TermFactory;
import charlie.substitution.Substitution;
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
  private ConstrainedSimplifier _simplifier;
  private EquationPosition _position;
  private String _hypothesisName;
  private boolean _inversed;

  /** Private constructor, called (only) by createStep */
  private DeductionHdelete(ProofState state, ProofContext context, String hypoName,
                            boolean inverse, EquationPosition pos, ConstrainedSimplifier s) {
    super(state, context);
    _simplifier = s;
    _position = pos;
    _hypothesisName = hypoName;
    _inversed = inverse;
  }

  /**
   * This returns null if s and t are the same, and otherwise a list of tuples (p,s|_p,t|_p) where
   * s|_p and t|_p are different.  Specifically, the positions in this list are in the order
   * p_n, p_{n-1}, ..., p_0 where p_0 = ε and each p_{i+1} is one position deeper than p_i, and
   * the contexts s[?]_{p_i} and t[?]_{p_i} are the same.
   */
  public static ArrayList<Pair<Position,Pair<Term,Term>>> contextDifferences(Term s, Term t) {
    ArrayList<Pair<Position,Pair<Term,Term>>> ret = null;
    // If the heads are not the same, we clearly are not part of a context surrounding a difference
    // (as we only consider argument contexts, not head contexts), so return [(ε,(s,t))].
    if (!s.queryHead().equals(t.queryHead()) || s.numberArguments() != t.numberArguments()) {
      ret = new ArrayList<Pair<Position,Pair<Term,Term>>>();
      ret.add(new Pair<Position,Pair<Term,Term>>(Position.empty, new Pair<Term,Term>(s,t)));
      return ret;
    }
    int n = s.numberArguments();
    // We have f(s1,...,sn) and f(t1,...,tn); find the first argument i where si != ti.
    int i = 1;
    for (; i <= n; i++) {
      ret = contextDifferences(s.queryArgument(i), t.queryArgument(i));
      if (ret != null) break;
    }
    // They don't differ anywhere? Then the terms are the same, so return null.
    if (ret == null) return ret;
    // If they differ in more than one spot, return [(ε,(s,t))] again.
    for (int j = i+1; j <= n; j++) {
      if (!s.queryArgument(j).equals(t.queryArgument(j))) {
        ret = new ArrayList<Pair<Position,Pair<Term,Term>>>();
        ret.add(new Pair<Position,Pair<Term,Term>>(Position.empty, new Pair<Term,Term>(s,t)));
        return ret;
      }
    }
    // If they only differ in one spot, then we are part of a suitable context!  The list is now
    // [(pn,pairn) ,..., (p1,pair1)]; replace it by [(i pn,pairn), ..., (i p1,pair1), (ε,(s,t))].
    for (int j = 0; j < ret.size(); j++) {
      ret.set(j, new Pair<Position,Pair<Term,Term>>(new ArgumentPos(i, ret.get(j).fst()),
                                                    ret.get(j).snd()));
    }
    ret.add(new Pair<Position,Pair<Term,Term>>(Position.empty, new Pair<Term,Term>(s,t)));
    return ret;
  }

  /**
   * Creates an hdelete step for the given information, checking that there is indeed a match but
   * NOT that the constraint is satisfied.
   * The substitution does not become the property of the step; it is safe to change afterwards.
   */
  public static DeductionHdelete createStep(PartialProof proof, Optional<OutputModule> m,
                                            Hypothesis hypo, boolean inverse,
                                            EquationPosition pos, Substitution subst) {
    Equation original = getTopEquation(proof.getProofState(), m);
    if (original == null) return null;

    ConstrainedSimplifier simpl =
      new ConstrainedSimplifier(inverse ? hypo.getRhs() : hypo.getLhs(),
                                inverse ? hypo.getLhs() : hypo.getRhs(),
                                hypo.getConstraint(), hypo.getRenaming(), subst);
    if (!simpl.matchSubterm(original, pos, m, "induction hypothesis")) return null;
    if (!matchRightSubterm(original, pos, simpl, m)) return null;
    simpl.matchEqualitiesInConstraint(original.getConstraint());
    Position p = pos.queryPosition();
    if (!sameContexts(original, p)) {
      m.ifPresent(o -> printBadContextError(proof.getProofState().getTopEquation(), p, o));
      return null;
    }
    if (!resultingOrderingRequirementOK(proof.getProofState().getTopEquation(), p, m)) return null;
    return new DeductionHdelete(proof.getProofState(), proof.getContext(),
                                hypo.getName() + (inverse ? "^{-1}" : ""), inverse, pos, simpl);
  }

  /**
   * If leftpos = Lp and eq = (s, C[t]_p), and simpl represents l → r | φ, this tries to extend the
   * underlying substitution γ of the simplifier so that t = r γ.
   */
  private static boolean matchRightSubterm(Equation eq, EquationPosition leftpos,
                                           ConstrainedSimplifier simpl, Optional<OutputModule> m) {
    EquationPosition.Side side = switch(leftpos.querySide()) {
      case EquationPosition.Side.Left -> EquationPosition.Side.Right;
      case EquationPosition.Side.Right -> EquationPosition.Side.Left;
    };
    String sd = switch(side) {
      case EquationPosition.Side.Left -> "left";
      case EquationPosition.Side.Right -> "right";
    };

    Term othersub = eq.querySubterm(new EquationPosition(side, leftpos.queryPosition()));
    if (othersub == null) {
      m.ifPresent(o -> o.println("The %a-hand side of the equation does not have a position %a.",
                                 sd, leftpos.queryPosition()));
      return false;
    }
    if (simpl.matchRight(othersub) != null) {
      m.ifPresent(o -> o.println("The induction hypothesis does not match the %a-hand side " +
        "of the equation.", sd));
      return false;
    }
    return true;
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
    return new ConstrainedReductionHelper(left, right, hequ.getConstraint(), hypo.getRenaming(),
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
    MutableRenaming renaming = ec.getRenaming().copy();
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
    if (_simplifier.constraintIsTrue()) return true;
    return _simplifier.canReduceCtermWithConstraint(_equ.getConstraint(), Settings.smtSolver,
                                          _equ.getRenaming(), module, "induction hypothesis");
  }

  @Override
  protected ProofState tryApply(Optional<OutputModule> module) {
    return _state.deleteTopEquation();
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("hdelete ", _hypothesisName, " ", _position, " with ",
      _simplifier.substitutionPrintable(_equ.getRenaming()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply HDELETE to %a with induction hypothesis %a and substitution %a.",
      _equ.getName(), _hypothesisName, _simplifier.substitutionPrintable(_equ.getRenaming()));
  }
}

