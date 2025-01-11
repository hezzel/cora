/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Optional;
import java.util.Stack;

import charlie.exceptions.IndexingException;
import charlie.util.Pair;
import charlie.terms.*;
import charlie.printer.ParseableTermPrinter;
import charlie.theorytranslation.TermAnalyser;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

public final class DeductionCalc extends DeductionStep {
  private List<EquationPosition> _position;  // position and replacement must always
  private List<Term> _replacement;           // have the same number of arguments
  private Term _newconstraint;               // null if no new constraint is to be added
  private HashMap<String,Variable> _newvars;

  private DeductionCalc(ProofState state, ProofContext context, List<EquationPosition> pos,
                     List<Term> replacement, Term constr, HashMap<String,Variable> newvars) {
    super(state, context);
    _position = pos;
    _replacement = replacement;
    _newconstraint = constr;
    _newvars = newvars;
  }
  
  /**
   * Helper function for both tryApply and explains: creates the Renaming that is to be used for
   * the resulting Equation.
   */
  private Renaming makeNewRenaming() {
    Renaming renaming = _equ.getRenaming();
    for (String name : _newvars.keySet()) { renaming.setName(_newvars.get(name), name); }
    return renaming;
  }

  /**
   * Applies the calculation step by simply replacing each of the given positions by the
   * corresponding replacement.  In addition, the constraint is amended with _newconstraint (if any
   * is given), and the Renaming is updated with _newvars.
   */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Term left = _equ.getEquation().getLhs();
    Term right = _equ.getEquation().getRhs();
    Term constraint = _equ.getEquation().getConstraint();

    // note that we cannot create a step where _position and _replacement have different lengths,
    // so we only use one of them as the iteration bound
    for (int i = 0; i < _position.size(); i++) {
      EquationPosition pos = _position.get(i);
      Term replacement = _replacement.get(i);
      switch (pos.querySide()) {
        case Left:
          left = left.replaceSubterm(pos.queryPosition(), replacement);
          break;
        case Right:
          right = right.replaceSubterm(pos.queryPosition(), replacement);
          break;
      }
    }

    if (_newconstraint != null) {
      constraint = TheoryFactory.createConjunction(constraint, _newconstraint);
    }

    Equation newequation = new Equation(left, right, constraint);
    EquationContext context;
    if (_newconstraint == null) context = _equ.replace(newequation, _state.getLastUsedIndex() + 1);
    else context = _equ.replace(newequation, makeNewRenaming(), _state.getLastUsedIndex() + 1);
    return _state.replaceTopEquation(context);
  }

  /**
   * There is nothing to verify: all the verification is necessarily in the createStep function.
   * Hence, if we can create the step at all (which must be the case if we get to this function),
   * then it must be applicable.
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    return true;
  }

  @Override
  public String commandDescription(ParseableTermPrinter printer) {
    StringBuilder ret = new StringBuilder("calc ");
    for (EquationPosition pos : _position) ret.append(pos.toString() + " ");
    return ret.toString().trim();
  }

  /** Prints a human-readable explanation. */
  @Override
  public void explain(OutputModule module) {
    if (_newconstraint != null) {
      Renaming renaming = makeNewRenaming();
      module.print("We use ALTER to add %a to the constraint, and then ",
        new Pair<Term,Renaming>(_newconstraint, renaming));
    }
    else module.print("We ");
    
    if (_position.size() == 1) module.print("use CALC at position ");
    else module.print("use CALC at positions ");
    
    for (int i = 0; i < _position.size(); i++) {
      if (i != 0 && i == _position.size() - 1) module.print(" and ");
      else if (i >= 1) module.print(", ");
      module.print("%a", _position.get(i));
    }
    module.println(".");
  }

  // ==============================================================================================
  // this deduction step has a very sophisticated createStep function, because for each position
  // there are three very different things we can do

  /**
   * Helper class for createStep: a mutable pair of two terms.  We will use this to pass around
   * the equation pair (not including the constraint) as we change it step-by-step, since the
   * equation itself is immutable.
   */
  private static class ChangeablePair {
    Term left;
    Term right;
    ChangeablePair(Term l, Term r) { left = l; right = r; }
    /** @throws IndexingException */
    Term subterm(EquationPosition pos) {
      return switch (pos.querySide()) {
        case EquationPosition.Side.Left -> left.querySubterm(pos.queryPosition());
        case EquationPosition.Side.Right -> right.querySubterm(pos.queryPosition());
      };
    }
    /** @throws IndexingException */
    void replace(EquationPosition pos, Term replacement) {
      if (pos.querySide() == EquationPosition.Side.Left) {
        left = left.replaceSubterm(pos.queryPosition(), replacement);
      }
      else right = right.replaceSubterm(pos.queryPosition(), replacement);
    }
  }

  /**
   * Creates a step that can execute simplifcation with a calculation rule at the given positions.
   * This will only succeed if ALL the given positions are calculatable, in the given order
   */
  public static Optional<DeductionCalc> createStep(PartialProof proof, Optional<OutputModule> m,
                                                   List<EquationPosition> posses) {
    Equation eq = getTopEquation(proof.getProofState(), m);
    if (eq == null) return Optional.empty();
    Renaming renaming = proof.getProofState().getTopEquation().getRenaming();
    HashMap<Term,Variable> definedVars = breakupConstraint(eq.getConstraint());
    ChangeablePair pair = new ChangeablePair(eq.getLhs(), eq.getRhs());
    Term constraint = TheoryFactory.trueValue;
    HashMap<String,Variable> newvars = new HashMap<String,Variable>();

    List<Term> replacements = new ArrayList<Term>();
    for (EquationPosition pos : posses) {
      Term newconstr = tryComputing(pos, pair, definedVars, newvars, replacements, renaming, eq, m);
      if (newconstr == null) return Optional.empty(); // error message has already been printed
      constraint = TheoryFactory.createConjunction(constraint, newconstr);
    }

    if (constraint.isValue()) constraint = null;

    return Optional.of(new DeductionCalc(proof.getProofState(), proof.getContext(), posses,
                                         replacements, constraint, newvars));
  }

  /**
   * Helper function for createStep: this applies a calculation step for a single position to the
   * given left/right pair.  For this, we may assume that all definitions in the constraint (both
   * original definitions, and definitions that were added for the calculations of previous
   * positions) are listed in definedVars.
   *
   * If the step cannot be applied then a message is potentially printed to the given output
   * module (which may use the given renaming for its term printing) and null returned; if it
   * can be applied, then the following things happen:
   * - the subterm at the given position is replaced by the value or variable that results from
   *   the computation
   * - this same replacement value/variable is added to the replacements list
   * - if the computation requires the addition of a term x = t to the constrained, then
   *   [t:=x] is added to definedVars, a name for x is added to the renaming and to newvars,
   *   and the term x = t is returned; otherwise true is returned (so the return value
   *   indicates a constraint that should be added to the equation's constraint before this
   *   calculation step can be done).
   */
  private static Term tryComputing(EquationPosition pos, ChangeablePair pair,
                                   HashMap<Term,Variable> definedVars,
                                   HashMap<String,Variable> newvars,
                                   List<Term> replacements, Renaming renaming,
                                   Equation original,
                                   Optional<OutputModule> m) {
    Term sub;
    try { sub = pair.subterm(pos); }
    catch (IndexingException e) {
      String msg;
      if (original.querySubterm(pos) == null) msg = "No such position: %a.";
      else msg = "Subterm at position %a has already been calculated away!";
      m.ifPresent(o -> o.println(msg, pos));
      return null;
    }

    if (!calculatable(sub)) {
      m.ifPresent(o -> o.println("The subterm %a at position %a is not calculatable: " +
        "it should be a first-order theory term.", sub, pos));
      return null;
    }

    Term replacement;
    Term ret = TheoryFactory.trueValue;
    if (sub.isGround()) replacement = TermAnalyser.evaluate(sub);
    else replacement = definedVars.get(sub);

    if (replacement == null) {
      Variable newvar = createNewVariable(sub, renaming, newvars);
      definedVars.put(sub, newvar);
      ret = TheoryFactory.createEquality(newvar, sub);
      replacement = newvar;
    }

    pair.replace(pos, replacement);
    replacements.add(replacement);

    return ret;
  }

  /**
   * This function checks if the given term satisfies the prerequisites of the calc rule: it is a
   * first-order theory term, so any value instantiation can be reduced using the calculation step
   * to a value.
   */
  private static boolean calculatable(Term term) {
    return term.isFunctionalTerm() &&
           term.isApplication() &&
           term.isTheoryTerm() &&
           term.isFirstOrder();
  }

  private static HashMap<Term,Variable> breakupConstraint(Term constraint) {
    HashMap<Term,Variable> ret = new HashMap<Term,Variable>();
    Stack<Term> todo = new Stack<Term>();
    todo.push(constraint);
    while (!todo.isEmpty()) {
      Term term = todo.pop();
      while (term.isFunctionalTerm() && term.queryRoot().equals(TheoryFactory.andSymbol) &&
             term.numberArguments() == 2) {
        todo.push(term.queryArgument(2));
        term = term.queryArgument(1);
      }
      if (!term.isFunctionalTerm() || term.numberArguments() != 2) continue;
      CalculationSymbol f = term.queryRoot().toCalculationSymbol();
      if (f == null) continue;
      if (f.queryKind() != CalculationSymbol.Kind.EQUALS &&
          f.queryKind() != CalculationSymbol.Kind.IFF) continue;
      if (term.queryArgument(1).isVariable() && !term.queryArgument(2).isVariable()) {
        ret.put(term.queryArgument(2), term.queryArgument(1).queryVariable());
      }
      if (term.queryArgument(2).isVariable() && !term.queryArgument(1).isVariable()) {
        ret.put(term.queryArgument(1), term.queryArgument(2).queryVariable());
      }
    }
    return ret;
  }

  /**
   * This function chooses a base name for a variable that is meant to replace the given term.
   * The real name (that will be added to the naming) will have the form <base><index>.
   */
  private static String chooseBaseName(Term term) {
    if (term.freeReplaceables().size() == 1) {
      for (Replaceable x : term.freeReplaceables()) return x.queryName();
    }
    return term.queryType().toString().substring(0,1).toLowerCase();
  }

  /**
   * This function chooses a fresh variable name for a Variable that is meant to replace the given
   * term, creates the variable, and adds the name both to newvars and to naming.
   */
  private static Variable createNewVariable(Term term, Renaming naming,
                                            HashMap<String,Variable> newvars) {
    String base = chooseBaseName(term);
    Variable ret = TermFactory.createVar(base, term.queryType());
    for (int i = 1; ; i++) {
      String attempt = base + i;
      if (naming.isAvailable(attempt) && !newvars.containsKey(attempt)) {
        newvars.put(attempt, ret);
        naming.setName(ret, attempt);
        return ret;
      }
    }
  }

}

