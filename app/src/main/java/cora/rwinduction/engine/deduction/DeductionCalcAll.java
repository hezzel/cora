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

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Optional;
import java.util.Stack;

import charlie.util.Pair;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.theorytranslation.TermAnalyser;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * The DeductionCalcAll step represents a combination of calculation steps: all calculation steps
 * in either one side of the equation, or both sides together, are done in one go.
 */
public final class DeductionCalcAll extends DeductionStep {
  public enum Side { Left, Right, Both };

  private Equation _newEquation;
  private MutableRenaming _newRenaming;
  private Side _side;
  private int _numReplacements;

  private DeductionCalcAll(ProofState state, ProofContext context,
                           Equation eq, MutableRenaming ren, int numreps, Side side) {
    super(state, context);
    _newEquation = eq;
    _newRenaming = ren;
    _numReplacements = numreps;
    _side = side;
  }
  
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    EquationContext ctxt = _equ.replace(_newEquation, _newRenaming, _state.getLastUsedIndex() + 1);
    return _state.replaceTopEquation(ctxt);
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
  public String commandDescription() {
    return switch (_side) {
      case Left -> "calc left";
      case Right -> "calc right";
      case Both -> "calc";
    };
  }

  /** Prints a human-readable explanation. */
  @Override
  public void explain(OutputModule module) {
    String location = switch(_side) {
      case Left -> " in the left-hand side of the equation";
      case Right -> " in the right-hand side of the equation";
      case Both -> "";
    };
    if (_numReplacements == 1) {
      module.println("We use CALC at the only position%a where it is possible.", location);
    }
    else {
      module.println("We use CALC at all %a positions%a where it is possible.",
                     _numReplacements, location);
    }
  }

  private static class ReplacementInfo {
    ArrayList<Term> freshVars;
    ArrayList<Term> varReplacements;
    int count;
    ReplacementInfo() {
      freshVars = new ArrayList<Term>();
      varReplacements = new ArrayList<Term>();
      count = 0;
    }
  }

  public static DeductionCalcAll createStep(PartialProof proof, Optional<OutputModule> m,
                                            Side side) {
    Equation eq = getTopEquation(proof.getProofState(), m);
    if (eq == null) return null;
    MutableRenaming renaming = proof.getProofState().getTopEquation().getRenamingCopy();
    HashMap<Term,Variable> definedVars = CalcHelper.breakupConstraint(eq.getConstraint());
    VariableNamer namer = proof.getContext().getVariableNamer();

    Term left = eq.getLhs();
    Term right = eq.getRhs();
    ReplacementInfo info = new ReplacementInfo();
    if (side == Side.Left || side == Side.Both) {
      left = doCalculations(left, definedVars, renaming, info, namer, null);
    }
    if (side == Side.Right || side == Side.Both) {
      right = doCalculations(right, definedVars, renaming, info, namer, null);
    }
    if (info.count == 0) {
      m.ifPresent(o -> o.println("There are no calculatable subterms."));
      return null;
    }

    Term constraint = buildConstraint(eq.getConstraint(), info);
    Equation neweq = new Equation(left, right, constraint);
    return new DeductionCalcAll(proof.getProofState(), proof.getContext(),
                                neweq, renaming, info.count, side);
  }

  /**
   * This does all calculations in term and returns the result, using info to store how much is
   * replaced and which new definitions should be added to the constraint.  The given map stores
   * [t→x] pairs if t = x occurs in the constraint, or has been added as a definition.  The given
   * renaming stores both the names for the variables in the term and the map, and is updated to
   * store the new names for the fresh variables.  The given parent is a pair <f,i> such that this
   * term is a term si inside f s1 ... sn, and may be null if that is not the case.
   */
  private static Term doCalculations(Term term, HashMap<Term,Variable> map,
                                     MutableRenaming renaming,
                                     ReplacementInfo info, VariableNamer namer,
                                     Pair<FunctionSymbol,Integer> parent) {
    if (CalcHelper.calculatable(term)) {
      info.count++;
      if (term.isGround()) return TermAnalyser.evaluate(term);
      Term replacement = map.get(term);
      if (replacement != null) return replacement;
      Variable x = namer.chooseDerivativeForTerm(term, renaming,
        term.queryType().toString().substring(0,1).toLowerCase(), parent);
      info.freshVars.add(x);
      info.varReplacements.add(term);
      map.put(term, x);
      return x;
    }
    return doCalculcationsRecurse(term, map, renaming, info, namer);
  }

  /**
   * Helper function for doCalculations: this recursively calls doCalculations on all subterms,
   * and combines the result into a single term.  If there is nothing to calculate, then the
   * original pointer is returned unmodified.
   *
   * We use a small optimisation, avoiding unnecessary allocations if nothing is changed.
   */
  private static Term doCalculcationsRecurse(Term term, HashMap<Term,Variable> map,
                                             MutableRenaming renaming, ReplacementInfo info,
                                             VariableNamer namer) {
    Term head = term.queryHead();
    ArrayList<Term> args = null;
    for (int i = 1; i <= term.numberArguments(); i++) {
      Term arg = term.queryArgument(i);
      Pair<FunctionSymbol,Integer> parent = head.isConstant() ?
        new Pair<FunctionSymbol,Integer>(head.queryRoot(), i) : null;
      Term replacement = doCalculations(arg, map, renaming, info, namer, parent);
      if (arg != replacement && args == null) {
        args = new ArrayList<Term>();
        for (int j = 1; j < i; j++) args.add(term.queryArgument(j));
      }
      if (args != null) args.add(replacement);
    }
    if (args == null) return term;
    return head.apply(args);
  }

  /**
   * Given that info contains replacements (x1, t1), ..., (xn, tn), this returns the constraint
   * base ∧ x1 = t1 ∧ ... ∧ xn = tn.
   */
  private static Term buildConstraint(Term base, ReplacementInfo info) {
    for (int i = 0; i < info.freshVars.size(); i++) {
      base = TheoryFactory.createConjunction(base,
        TheoryFactory.createEquality(info.freshVars.get(i), info.varReplacements.get(i)));
    }
    return base;
  }
}

