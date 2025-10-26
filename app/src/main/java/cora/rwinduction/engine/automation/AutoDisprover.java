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

package cora.rwinduction.engine.automation;

import java.util.ArrayList;
import java.util.Optional;
import charlie.types.Type;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.*;
import charlie.substitution.Substitution;
import charlie.substitution.MutableSubstitution;
import charlie.printer.Printer;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.EquationContext;
import cora.rwinduction.engine.DeductionStep;
import cora.rwinduction.engine.PartialProof;
import cora.rwinduction.engine.deduction.DeductionDisproveTheory;
import cora.rwinduction.engine.deduction.DeductionDisproveRoot;

/**
 * This class automates finding a DISPROVE step that can be applied to deduce a contradiction in a
 * given equation.
 */
public final class AutoDisprover {
  /**
   * This automatically finds either a DeductionDisproveRoot or a DeductionDisproveTheory step
   * that can be applied to the current top equation, if there is any.
   */
  public static DeductionStep createStep(PartialProof proof, Optional<OutputModule> module) {
    EquationContext ec = proof.getProofState().getTopEquation();
    Term left = ec.getLhs();
    Term right = ec.getRhs();

    if (left.queryType().isBaseType() && left.isTheoryTerm() && right.isTheoryTerm()) {
      Substitution subst = findContradictingTheorySubstitution(left, right, ec.getConstraint(),
                                                               module, ec.getRenaming());
      if (subst == null) return null;
      return DeductionDisproveTheory.createStep(proof, module, subst);
    }
    else {
      return DeductionDisproveRoot.createStep(proof, module);
    }
  }

  /**
   * This automatically finds a DeductionDisproveTheory step that can be applied to the current
   * top equation, if there is any.
   */
  public static DeductionDisproveTheory createTheoryStep(PartialProof proof,
                                                         Optional<OutputModule> module) {
    EquationContext ec = proof.getProofState().getTopEquation();
    Substitution subst = findContradictingTheorySubstitution(ec.getLhs(), ec.getRhs(),
                                        ec.getConstraint(), module, ec.getRenaming());
    if (subst == null) return null;
    return DeductionDisproveTheory.createStep(proof, module, subst);
  }

  /**
   * This method tries to find a substitution γ so that c γ is strue, yet l γ != r γ.
   * This does typically cause one or more calls to the SMT-solver.
   *
   * In case of failure, null is returned and an appropriate message printd on the output module.
   *
   * If an output module is given, then the renaming should contain the variables used in l, r
   * and c, as it may be used for error messages.
   */
  public static Substitution findContradictingTheorySubstitution(Term l, Term r, Term c,
                                       Optional<OutputModule> module, Renaming renaming) {
    if (!l.queryType().isBaseType() || !r.queryType().isBaseType()) {
      module.ifPresent(o -> o.println("Theory disproves can only be done if both sides of the " +
        "equation have base type."));
        return null;
    }
    if (!l.isTheoryTerm() || !r.isTheoryTerm()) {
      module.ifPresent(o -> o.println("Theory disproves can only be done if both sides of the " +
        "equation are theory terms."));
        return null;
    }
    if (l.isFirstOrder() && r.isFirstOrder()) return findBaseSubstitution(l,r,c,module,renaming);
    else return findHigherOrderSubstitution(l, r, c, module, renaming);
  }

  /**
   * This method handles the case for findContradictingTheorySubstitution where both sides are
   * first-order terms: the SMT solver should be able to verify or discard this case on its own.
   */
  public static Substitution findBaseSubstitution(Term l, Term r, Term c,
                        Optional<OutputModule> module, Renaming renaming) {
    // combi =  c ∧ l != r
    Term combi = TheoryFactory.createConjunction(c,
      TheoryFactory.notSymbol.apply(TheoryFactory.createEquality(l, r)));
    switch (TermAnalyser.satisfy(combi, Settings.smtSolver)) {
      case TermAnalyser.Result.YES(Substitution subst):
        return subst;
      case TermAnalyser.Result.NO():
        module.ifPresent(o -> o.println("DISPROVE cannot be applied because %a is unsatisfiable; " +
          "try EQ-DELETE instead!", Printer.makePrintable(combi, renaming)));
        return null;
      case TermAnalyser.Result.MAYBE(String reason):
        module.ifPresent(o -> o.println("Failed to apply DISPROVE, because the SMT solver " +
          "cannot prove or disprove satisfiability of %a (the solver says \"%a\").",
          Printer.makePrintable(combi, renaming), reason));
        return null;
    }
  }

  /**
   * This method handles the case for findContradictingTheorySubstitution where the equation uses
   * some higher-order variable.  In this case, we try all possible combinations of instantiations
   * of the higher-order variables.
   */
  public static MutableSubstitution findHigherOrderSubstitution(Term l, Term r, Term c,
                                      Optional<OutputModule> module, Renaming renaming) {
    ArrayList<Variable> variables = getHOVars(l, r);
    ArrayList<ArrayList<Term>> instances = getHOInstances(variables, renaming, module);
    if (instances == null) return null;

    // iterate over all combinations until we find one that works; we do this by ensuring
    // that current is a list [j1,...,jn] where 0 ≤ ji ≤ |lsti|, and step-by-step increasing
    // this list lexicographically and building the corresponding substitution with
    // variables[i] := instances[i][ji]
    ArrayList<Integer> current = new ArrayList<Integer>();
    for (int i = 0; i < variables.size(); i++) current.add(0);
    MutableSubstitution subst = new MutableSubstitution();
    for (int pos = 0; pos >= 0; ) {
      if (pos == variables.size()) {
        if (findFirstOrderInstance(l, r, c, subst)) return subst;
        pos--;
      }
      int k = current.get(pos);
      if (k == instances.get(pos).size()) {
        subst.delete(variables.get(pos));
        current.set(pos, 0);
        pos--;
        continue;
      }
      subst.replace(variables.get(pos), instances.get(pos).get(k));
      current.set(pos, k+1);
      pos++;
    }

    module.ifPresent(o -> o.println("No substitution could be found that makes %a true and " +
      "%a %{distinct} %a.  If such a substitution does exist, please supply it manually.",
      Printer.makePrintable(c, renaming), Printer.makePrintable(l, renaming),
      Printer.makePrintable(r, renaming)));
    return null;
  }

  /**
   * Helper function for findContradictingTheorySubstitution: returns all higher-order variables in
   * left/right.
   */
  private static ArrayList<Variable> getHOVars(Term left, Term right) {
    ArrayList<Variable> variables = new ArrayList<Variable>();
    for (Variable x : left.vars()) {
      if (!x.queryType().isBaseType()) variables.add(x);
    }
    for (Variable x : right.vars()) {
      if (!left.freeReplaceables().contains(x) && !x.queryType().isBaseType()) variables.add(x);
    }
    return variables;
  }

  /**
   * Helper function for findContradictingTheorySubstitution: this returns a list that contains,
   * for each of the given higher-order variables, a list of all instance shapes that can be
   * created using calculation symbols and fresh variables.  If it returns null, then some variable
   * is not instantiable (and an error message has already been given).
   */
  private static ArrayList<ArrayList<Term>> getHOInstances(ArrayList<Variable> variables,
                                                           Renaming renaming,
                                                           Optional<OutputModule> module) {
    ArrayList<ArrayList<Term>> instances = new ArrayList<ArrayList<Term>>();
    for (int i = 0; i < variables.size(); i++) {
      ArrayList<Term> inst = getAllInstances(variables.get(i).queryType());
      if (inst.size() == 0) {
        Variable x = variables.get(i);
        module.ifPresent(o -> o.println("There are no standard calculation symbols that " +
          "could be used to instantiate the higher-order variable %a (of type %a).",
          renaming.getName(x), x.queryType()));
        return null;
      }
      instances.add(inst);
    }
    return instances;
  }

  /**
   * Helper function for getHOInstances: this function returns all terms of the form
   * f(x1,...,xn) so that f is a calculation symbol, x1,...,xn are fresh variables, and
   * f(x1,...,xn) has type otype.
   */
  static ArrayList<Term> getAllInstances(Type otype) {
    int oar = otype.queryArity();
    ArrayList<Term> ret = new ArrayList<Term>();
    for (FunctionSymbol f : TheoryFactory.queryAllCalculationSymbols()) {
      Type t = f.queryType();
      int k = t.queryArity();
      if (k < oar) continue;
      int n = k - oar;
      for (int i = 0; i < n; i++) t = t.subtype(2);
      if (!t.equals(otype)) continue;
      Term term = f;
      for (int i = 0; i < n; i++) {
        term = term.apply(TermFactory.createVar(term.queryType().subtype(1)));
      }
      ret.add(term);
    }
    return ret;
  }

  /**
   * Given that all higher-order variables in left, right and constraint are instantiated by
   * first-order theory terms in gamma, this function tries to find a substitution delta so that
   * constraint gamma delta holds, and left gamma delta != right gamma delta.
   *
   * If successful, true is returned, and gamma updated to be the limitation of gamma delta whose
   * domain only contains variables in left, right and constraint.
   *
   * If unsuccessful, false is returned, and gamma is not changed.
   */
  private static boolean findFirstOrderInstance(Term left, Term right, Term constraint,
                                                MutableSubstitution gamma) {
    Substitution delta = findBaseSubstitution(gamma.substitute(left), gamma.substitute(right),
                                              gamma.substitute(constraint), Optional.empty(),
                                              null);
    if (delta == null) return false;
    gamma.combine(delta);
    ArrayList<Replaceable> remove = new ArrayList<Replaceable>();
    for (Replaceable x : gamma.domain()) {
      if (!left.freeReplaceables().contains(x) && !right.freeReplaceables().contains(x) &&
          !constraint.freeReplaceables().contains(x)) {
        remove.add(x);
      }
    }
    for (Replaceable x : remove) gamma.delete(x);
    return true;
  }
}

