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
import java.util.List;
import java.util.Optional;
import charlie.util.Pair;
import charlie.terms.position.Position;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This class represents a derived deduction rule: EQ-DELETE takes an equation of the form
 * C[s1,...,sn] = C[t1,...,tn] | φ where all si and ti are values or variables and φ implies
 * that each si = ti.  The command ALTER to replace each si by ti, and then uses DELETE to remove
 * the equation.
 */
public final class DeductionEqdelete extends DeductionStep {
  private Term _required;

  private DeductionEqdelete(ProofState state, ProofContext context,
                            ArrayList<Pair<Term,Term>> equalParts) {
    super(state, context);
    _required = TheoryFactory.createValue(true);
    for (Pair<Term,Term> pair : equalParts) {
      Term c = TheoryFactory.createEquality(pair.fst(), pair.snd());
      _required = TheoryFactory.createConjunction(_required, c);
    }
  }
 
  public static Optional<DeductionEqdelete> createStep(PartialProof proof,
                                                       Optional<OutputModule> module) {
    ProofState state = proof.getProofState();
    Equation eq = DeductionStep.getTopEquation(state, module);
    if (eq == null) return Optional.empty();

    ArrayList<Pair<Term,Position>> posLeft = getSubtermInfo(eq.getLhs());
    ArrayList<Pair<Term,Position>> posRight = getSubtermInfo(eq.getRhs());

    if (!checkSamePositions(posLeft, posRight, module)) return Optional.empty();

    Renaming renaming = state.getTopEquation().getRenaming();
    ArrayList<Pair<Term,Term>> parts = new ArrayList<Pair<Term,Term>>();

    int k = posLeft.size();
    for (int i = 0; i < k; i++) {
      Term a = posLeft.get(i).fst(), b = posRight.get(i).fst();
      boolean ok;
      if ((a.isVariable() || a.isConstant()) && (b.isVariable() || b.isConstant())) {
        ok = checkDifferencesAreTheory(a, b, parts, renaming, module);
      }
      else ok = checkSameShape(a, b, renaming, module);
      if (!ok) return Optional.empty();
    }

    if (parts.size() == 0) {
      module.ifPresent(o -> o.println("No subterms to be equated; use DELETION instead!"));
      return Optional.empty();
    }

    return Optional.of(new DeductionEqdelete(state, proof.getContext(), parts));
  }

  /**
   * Helper function for createStep: given a term, this returns its subterm/position list cast to
   * an ArrayList.
   */
  private static ArrayList<Pair<Term,Position>> getSubtermInfo(Term t) {
    List<Pair<Term,Position>> info = t.querySubterms();
    if (info instanceof ArrayList<Pair<Term,Position>> a) return a;
    else return new ArrayList<Pair<Term,Position>>(info);
  }

  /**
   * Helper function for createStep: given a pair of subterm / position lists, this verifies that
   * they both have the exact same positions.
   */
  private static boolean checkSamePositions(ArrayList<Pair<Term,Position>> left,
                                            ArrayList<Pair<Term,Position>> right,
                                            Optional<OutputModule> module) {
    int k = left.size();
    if (k != right.size()) {
      module.ifPresent(o -> o.println("There is no suitable context for both sides: they have a " +
        "different number of subterms (note that you can only use EQ-DELETE if the terms to be " +
        "equated are variables or values -- not more sophisticated theory terms)."));
      return false;
    }

    for (int i = 0; i < k; i++) {
      if (!left.get(i).snd().equals(right.get(i).snd())) {
        module.ifPresent(o -> o.println("There is no suitable context for both sides: their " +
          "position lists are not the same."));
        return false;
      }
    }

    return true;
  }
  
  /**
   * Helper function for createStep: given a pair of terms that are not both leaf terms, this
   * verifies that they have the same outer shape; that is, they are both an application with
   * the same head, or they are both a tuple with the same length.
   */
  private static boolean checkSameShape(Term left, Term right, Renaming renaming,
                                        Optional<OutputModule> module) {
    if (left.isApplication()) {
      if (right.isApplication() && left.numberArguments() == right.numberArguments() &&
          left.queryHead().equals(right.queryHead())) return true;
    }
    else if (left.isTuple()) {
      if (right.isTuple() && left.numberTupleArguments() == right.numberTupleArguments()) {
        return true;
      }
    }
    else if (left.isVariable() || left.isConstant()) {
      module.ifPresent(o -> o.println("Subterm %a is a kind of term that is not currently " +
        "supported in the rewriting induction module (at least not in EQ-DELETION).",
        Printer.makePrintable(right, renaming)));
      return false;
    }
    else {
      module.ifPresent(o -> o.println("Subterm %a is a kind of term that is not currently " +
        "supported in the rewriting induction module (at least not in EQ-DELETION).",
        Printer.makePrintable(left, renaming)));
      return false;
    }

    module.ifPresent(o -> o.println("There is no suitable context for both sides: subterms " +
      "%a and %a cannot be equated.",
      Printer.makePrintable(left, renaming), Printer.makePrintable(right, renaming)));
    return false;
  }

  /**
   * Helper function for createStep: given that left and right are both leaf terms (variables or
   * constants), this checks that they are either the same, or base-type theory terms that can be
   * put into the constraint; and in the latter case, the triple is added into parts.
   */
  private static boolean checkDifferencesAreTheory(Term left, Term right,
                                                   ArrayList<Pair<Term,Term>> parts,
                                                   Renaming renaming,
                                                   Optional<OutputModule> module) {

    if (left.equals(right)) return true;
    
    if (left.isConstant() && right.isConstant()) {
      String kind = left.isValue() ? "values" : "constants";
      module.ifPresent(o -> o.println("Failed to equate distinct %a (%a and %a).",
        kind, Printer.makePrintable(left, renaming), Printer.makePrintable(right, renaming)));
      return false;
    }
      
    if ( (!left.isVariable() && !left.isValue()) || (!right.isVariable() && !right.isValue()) ) {
      Term bad = (left.isVariable() || left.isValue()) ? right : left;
      module.ifPresent(o -> o.println("Failed to equate %a and %a: they cannot be moved into " +
        "the constraint because %a is not a theory term.",
        Printer.makePrintable(left, renaming), Printer.makePrintable(right, renaming),
        Printer.makePrintable(bad, renaming)));
      return false;
    }

    if (!left.queryType().isTheoryType() || !left.queryType().isBaseType()) {
      module.ifPresent(o -> o.println("Failed to equate %a and %a: they cannot be moved into " +
        "the constraint because the type %a is not a theory sort.",
        Printer.makePrintable(left, renaming), Printer.makePrintable(right, renaming),
        left.queryType()));
      return false;
    }

    parts.add(new Pair<Term,Term>(left, right));
    return true;
  }

  /**
   * Do all the heavy checks required before executing a step.  Since a DeductionDelete can only be
   * created through createStep, we may assume that the proof state is non-empty, so there is in
   * fact an equation to delete.
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    TermSmtTranslator translator = new TermSmtTranslator();
    translator.requireImplication(_equ.getEquation().getConstraint(), _required);
    if (Settings.smtSolver.checkValidity(translator.queryProblem())) return true;
    Renaming renaming = _equ.getRenaming();
    module.ifPresent(o -> o.println("The EQ-DELETION rule is not obviously applicable: " +
      "I could not prove that %a %{Vdash} %a.",
      Printer.makePrintable(_equ.getEquation().getConstraint(), renaming),
      Printer.makePrintable(_required, renaming)));
    return false;
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    return _state.deleteTopEquation();
  }

  @Override
  public String commandDescription() {
    return "eq-delete";
  }

  @Override
  public void explain(OutputModule module) {
    Renaming renaming = _equ.getRenaming();
    module.println("We observe that %a %{Vdash} %a, and may therefore apply EQ-DELETION to " +
      "remove %a from the proof state.",
      Printer.makePrintable(_equ.getEquation().getConstraint(), renaming),
      Printer.makePrintable(_required, renaming),
      _equ.getName());
  }
}

