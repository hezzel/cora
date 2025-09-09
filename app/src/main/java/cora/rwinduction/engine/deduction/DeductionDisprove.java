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
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;
import charlie.util.Pair;
import charlie.types.Base;
import charlie.types.Type;
import charlie.terms.replaceable.*;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.smt.*;
import charlie.theorytranslation.TermAnalyser;
import charlie.theorytranslation.TermSmtTranslator;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** This deduction step handles both instances of the "disprove" case. */
public abstract class DeductionDisprove extends DeductionStep {
  protected DeductionDisprove(ProofState state, ProofContext context) {
    super(state, context);
  }

  @Override
  public final ProofState tryApply(Optional<OutputModule> module) {
    return ProofState.getContradictionState();
  }

  @Override
  public final String commandDescription() {
    return "disprove";
  }

  public static DeductionDisprove createStep(PartialProof proof, Optional<OutputModule> m) {
    ProofState state = proof.getProofState();
    ProofContext context = proof.getContext();
    Equation equation = getTopEquation(proof.getProofState(), m); 
    if (equation == null) return null;
    Term left = equation.getLhs();
    Term right = equation.getRhs();
    
    if (state.getIncompleteEquations().contains(state.getTopEquation().getIndex())) {
      m.ifPresent(o -> o.println("DISPROVE can only be applied on complete equation contexts."));
      return null;
    }

    if (left.queryType().isBaseType() && left.isTheoryTerm() && right.isTheoryTerm()) {
      if (left.isFirstOrder() && right.isFirstOrder()) {
        return new DeductionDisproveFOTheory(state, context);
      }
      else {
        ArrayList<Substitution> possible = new ArrayList<Substitution>();
        Renaming renaming = state.getTopEquation().getRenaming();
        if (!addPossibleSubstitutions(left, right, context, possible, renaming, m)) return null;
        return new DeductionDisproveHOTheory(state, context, possible);
      }
    }
    else {
      Pair<FunctionSymbol,FunctionSymbol> p = checkDifferentSemiconstructors(left, right, context);
      if (p == null) {
        m.ifPresent(o -> o.println("There is no substitution over the known alphabet that would " +
          "instantiate the left- and right-hand to different semi-constructor terms, nor are the " +
          "left- and right-hand side base-type theory terms."));
        return null;
      }
      return new DeductionDisproveSemi(state, context, p.fst(), p.snd());
    }
  }

  /**
   * If the top equation in the current proof state has a left-hand side and right-hand side that
   * can be instantiated to semi-constructor terms with different function symbols at the roots,
   * then this returns the pair of symbols that we can have at the root.
   * Otherwise, it returns null.
   */
  static Pair<FunctionSymbol,FunctionSymbol> checkDifferentSemiconstructors(Term left, Term right,
                                                                            ProofContext context) {
    if (left.queryHead().equals(right.queryHead())) return null;
    FunctionSymbol f = null, g = null;
    if (left.isFunctionalTerm()) {
      f = left.queryRoot();
      if (left.numberArguments() >= context.queryRuleArity(f)) return null;
    }
    if (right.isFunctionalTerm()) {
      g = right.queryRoot();
      if (right.numberArguments() >= context.queryRuleArity(g)) return null;
    }
    if (f != null && g != null) return new Pair<FunctionSymbol,FunctionSymbol>(f, g);

    // at least one side is (headed by) a variable -- see if there are different function symbols
    // that may be used to instantiate the head variables
    if (f == null) {
      f = findSemiConstructor(context, left.queryHead().queryType(), left.numberArguments(), g);
    }
    if (g == null) {
      g = findSemiConstructor(context, right.queryHead().queryType(), right.numberArguments(), f);
    }
    if (f != null && g != null) return new Pair<FunctionSymbol,FunctionSymbol>(f, g);
    return null;
  }

  /**
   * This returns a function symbol f so that arguments a1...an exist such that:
   * - f(a1,...,an) has type otype
   * - f has rule arity > n + numargs
   * - f is not h (note that h is allowed to be null, in which case nothing is excluded)
   * - f is not a value
   * If such a function symbol f does not exist, then null is returned instead.
   */
  private static FunctionSymbol findSemiConstructor(ProofContext context, Type otype,
                                                    int numargs, FunctionSymbol h) {
    HashSet<FunctionSymbol> set = new HashSet<FunctionSymbol>();
    set.addAll(TheoryFactory.queryAllCalculationSymbols());
    set.addAll(context.getTRS().queryAlphabet().getSymbols());
    int oar = otype.queryArity();
    for (FunctionSymbol f : set) {
      if (f == h) continue;
      // compute n knowing that IF f(a1,...,an) :: otype, then arity(f) = n + arity(otype),
      // so n = arity(f) - arity(otype) ≥ 0
      Type t = f.queryType();
      int k = t.queryArity();
      if (k < oar) continue;
      int n = k - oar;
      // check: f has rule arity > n + numargs
      if (context.queryRuleArity(f) <= n + numargs) continue;
      // check: the type of f(a1,...,an) is indeed otype
      for (int i = 0; i < n; i++) t = t.subtype(2);
      if (t.equals(otype)) return f;
    }
    return null;
  }

  /**
   * This function returns all terms of the form f(x1,...,xn) so that f is a function in set,
   * x1,...,xn are fresh variables, and f(x1,...,xn) has type otype.
   */
  static ArrayList<Term> getAllInstances(Set<CalculationSymbol> set, Type otype) {
    int oar = otype.queryArity();
    ArrayList<Term> ret = new ArrayList<Term>();
    for (FunctionSymbol f : set) {
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
   * Helper function for addPossibleSubstitutions: returns all higher-order variables in left/right
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
   * Helper function for addPossibleSubstitutions: this returns a list that contains, for each of
   * the given variables, a list of all instance shapes that can be created using calculation
   * symbols and fresh variables.  If it returns null, then some variable is not instantiable (and
   * an error message has already been given).
   */
  private static ArrayList<ArrayList<Term>> getHOInstances(ArrayList<Variable> variables,
                                                           Renaming renaming,
                                                           Optional<OutputModule> module) {
    ArrayList<ArrayList<Term>> instances = new ArrayList<ArrayList<Term>>();
    Set<CalculationSymbol> set = TheoryFactory.queryAllCalculationSymbols();
    for (int i = 0; i < variables.size(); i++) {
      ArrayList<Term> inst = getAllInstances(set, variables.get(i).queryType());
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
   * This function finds all higher-order variables in the theory terms left/right, and considers
   * all possible combinations of substitutions that turn both sides into a first-order theory
   * term.
   * If there is any variable that cannot be instantiated, then false is returned; if successful,
   * then true is returned.
   *
   * Default rather than private only for the sake of unit testing (this is quite complex code).
   */
  static boolean addPossibleSubstitutions(Term left, Term right, ProofContext context,
                                          ArrayList<Substitution> options,
                                          Renaming renaming,
                                          Optional<OutputModule> module) {
    ArrayList<Variable> variables = getHOVars(left, right);
    ArrayList<ArrayList<Term>> instances = getHOInstances(variables, renaming, module);
    if (instances == null) return false;

    // iteratively generate all possible combinations
    ArrayList<Integer> current = new ArrayList<Integer>();
    for (int i = 0; i < variables.size(); i++) current.add(0);
    Substitution subst = TermFactory.createEmptySubstitution();
    for (int pos = 0; pos >= 0; ) {
      if (pos == variables.size()) {
        options.add(subst.copy());
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

    return true;
  }
}

class DeductionDisproveSemi extends DeductionDisprove {
  private FunctionSymbol _left;
  private FunctionSymbol _right;

  DeductionDisproveSemi(ProofState state, ProofContext context,
                        FunctionSymbol left, FunctionSymbol right) {
    super(state, context);
    _left = left;
    _right = right;
  }

  @Override
  public boolean verify(Optional<OutputModule> m) {
    return true;
  }

  @Override
  public void explain(OutputModule module) {
    String extra1 = _left.queryType().equals(_equ.getEquation().getLhs().queryType()) ? "" : "(...)";
    String extra2 = _right.queryType().equals(_equ.getEquation().getRhs().queryType()) ? "" : "(...)";
    module.println("We apply DISPROVE to %a, which succeeds because the sides can be " +
      "instantiated to distinct semi-constructor terms; respectively %a%a and %a%a.",
        _equ.getName(), _left.queryName(), extra1, _right.queryName(), extra2);
  }
}

class DeductionDisproveFOTheory extends DeductionDisprove {
  private Substitution _substitution;
    // if not null, this is a substitution that makes the constraint of the equation true, but the
    // two sides unequal; this is only set by the verify step, so the deduction step is functional
    // without it

  DeductionDisproveFOTheory(ProofState state, ProofContext context) {
    super(state, context);
    _substitution = null;
  }

  private Term makeConstraint() {
    Equation eq = _equ.getEquation();
    return TheoryFactory.createConjunction(eq.getConstraint(),
      TheoryFactory.notSymbol.apply(TheoryFactory.createEquality(eq.getLhs(), eq.getRhs())));
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    Term constraint = makeConstraint();
    switch (TermAnalyser.satisfy(constraint, Settings.smtSolver)) {
      case TermAnalyser.Result.YES(Substitution subst):
        _substitution = subst;
        return true;
      case TermAnalyser.Result.NO():
        println(module, "DISPROVE cannot be applied because the constraint %a is unsatisfiable; " +
          "try DELETE instead!", Printer.makePrintable(constraint, _equ.getRenaming()));
        return false;
      case TermAnalyser.Result.MAYBE(String reason):
        println(module, "Failed to apply DISPROVE, because the SMT solver cannot prove or " +
          "disprove satisfiability of %a (the solver says \"%a\").",
          Printer.makePrintable(constraint, _equ.getRenaming()), reason);
        return false;
    }
  }

  @Override
  public void explain(OutputModule module) {
    if (_substitution == null) {
      module.println("We apply DISPROVE to %a, which succeeds because the constraint %a is " +
        "satisfiable.", _equ.getName(),
        Printer.makePrintable(makeConstraint(), _equ.getRenaming()));
    }
    else {
      Value l = TermAnalyser.evaluate(_equ.getEquation().getLhs().substitute(_substitution));
      Value r = TermAnalyser.evaluate(_equ.getEquation().getRhs().substitute(_substitution));
      Renaming renaming = _equ.getRenaming();
      module.println("We apply DISPROVE to %a, which succeeds because under the substitution %a, " +
        "the constraint %a evaluates to true, while the sides of the equation can be calculated " +
        "to %a and %a respectively.", _equ.getName(),
        Printer.makePrintable(_substitution, _equ.getRenaming(), _equ.getRenaming()),
        _equ.getEquation().getConstraint(), l, r);
    }
  }
}

class DeductionDisproveHOTheory extends DeductionDisprove {
  // each of the possibilities, when applied to left- and right-hand side of the equation, rsults
  // in first-order theory terms
  private ArrayList<Substitution> _possibilities;
  private Substitution _success;

  /** possibilities must be non-empty */
  DeductionDisproveHOTheory(ProofState state, ProofContext context,
                            ArrayList<Substitution> possibilities) {
    super(state, context);
    _possibilities = possibilities;
    _success = null;
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    Variable choice = TheoryFactory.createIntVar("choice");
    Term constr = makeConstraint(choice);
    switch (TermAnalyser.satisfy(constr, Settings.smtSolver)) {
      case TermAnalyser.Result.YES(Substitution subst):
        _success = _possibilities.get(subst.get(choice).toValue().getInt());
        _success.substitute(subst);
        _success.delete(choice);
        for (Replaceable x : subst.domain()) {
          if (!_equ.getEquation().getLhs().freeReplaceables().contains(x) &&
              !_equ.getEquation().getRhs().freeReplaceables().contains(x) &&
              !_equ.getEquation().getConstraint().freeReplaceables().contains(x)) {
            _success.delete(x);
          }
        }
        return true;
      default:
        println(module, "Failed to apply DISPROVE, because the SMT solver cannot prove " +
          "satisfiability of %a.", Printer.makePrintable(constr, _equ.getRenaming()));
        return false;
    }
  }

  private Term makeConstraint(Variable choice) {
    Term constraint = _equ.getEquation().getConstraint();
    Term left = _equ.getEquation().getLhs();
    Term right = _equ.getEquation().getRhs();
    // for each possible substitution, create the constraint choice = i ∧ left γ_i != right γ_i
    Term disjunction = null;
    for (int i = 0; i < _possibilities.size(); i++) {
      Term choiceisi = TheoryFactory.createEquality(choice, TheoryFactory.createValue(i));
      Term lgammai = left.substitute(_possibilities.get(i));
      Term rgammai = right.substitute(_possibilities.get(i));
      Term unequal = TheoryFactory.notSymbol.apply(TheoryFactory.createEquality(lgammai, rgammai));
      Term combi = TheoryFactory.createConjunction(choiceisi, unequal);
      if (disjunction == null) disjunction = combi;
      else disjunction = TermFactory.createApp(TheoryFactory.orSymbol, disjunction, combi);
    }
    return TheoryFactory.createConjunction(constraint, disjunction);
  }

  @Override
  public void explain(OutputModule module) {
    if (_success == null) {
      Variable choice = TheoryFactory.createIntVar("choice");
      MutableRenaming renaming = _equ.getRenaming().copy();
      if (!renaming.setName(choice, "choice")) {
        for (int i = 1; !renaming.setName(choice, "choice" + i); i++);
      }
      module.println("We apply DISPROVE to %a, which succeeds because the constraint %a is " +
        "satisfiable.", _equ.getName(), Printer.makePrintable(makeConstraint(choice), renaming));
    }
    else {
      Value l = TermAnalyser.evaluate(_equ.getEquation().getLhs().substitute(_success));
      Value r = TermAnalyser.evaluate(_equ.getEquation().getRhs().substitute(_success));
      Renaming renaming = _equ.getRenaming();
      module.println("We apply DISPROVE to %a, which succeeds because under the substitution %a, " +
        "the constraint %a evaluates to true, while the sides of the equation can be calculated " +
        "to %a and %a respectively.", _equ.getName(),
        Printer.makePrintable(_success, _equ.getRenaming(), _equ.getRenaming()),
        _equ.getEquation().getConstraint(), l, r);
    }
  }
}

