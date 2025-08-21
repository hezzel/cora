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
import java.util.Set;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

public final class DeductionCase extends DeductionStep {
  // note that multiple copies of ExtraInfo may share the same substitution and renaming; this is
  // treated as a read-only resource
  private record ExtraInfo(Substitution subst, Term constraint, Renaming renaming) {}
  private Term _term;
  private ArrayList<ExtraInfo> _cases;

  private DeductionCase(ProofState state, ProofContext context, Term term,
                        ArrayList<ExtraInfo> cases) {
    super(state, context);
    _term = term;
    _cases = cases;
  }
 
  public static DeductionCase createStep(PartialProof proof,
                                         Optional<OutputModule> module, Term caseterm) {
    ProofState state = proof.getProofState();
    Equation eq = DeductionStep.getTopEquation(state, module);
    if (eq == null) return null;
    Renaming renaming = state.getTopEquation().getRenaming();
    ArrayList<ExtraInfo> ret = new ArrayList<ExtraInfo>();

    if (caseterm.queryType().equals(TypeFactory.boolSort)) {
      if (!createBooleanCases(caseterm, renaming, module, ret)) return null;
    }
    else if (caseterm.queryType().equals(TypeFactory.intSort)) {
      if (!createIntegerCases(caseterm, renaming, module, ret)) return null;
    }
    else if (!nonTheoryCasesApplicable(caseterm, renaming, module)) return null;
    else {
      createConstructorCases(caseterm.queryVariable(), renaming, proof.getContext(), ret);
      if (caseterm.queryType().isProductType()) {
        createTupleCase(caseterm.queryVariable(), renaming, proof.getContext(), ret);
      }
    }
    return new DeductionCase(state, proof.getContext(), caseterm, ret);
  }

  /**
   * Helper function for createStep: given that caseterm is a boolean, this checks whether
   * it is a constraint, and if so, updates ret with the cases caseterm and ¬caseterm.
   * If not, then an appropriate error message is printed and false is returned.
   */
  private static boolean createBooleanCases(Term caseterm, Renaming renaming,
                                            Optional<OutputModule> module,
                                            ArrayList<ExtraInfo> ret) {
    if (!caseterm.isTheoryTerm() || !caseterm.isFirstOrder()) {
      module.ifPresent(m -> m.println("Cannot do case analysis on %a: this is a boolean term, " +
        "but not a first-order theory term, so it cannot be added to the constraint.",
        Printer.makePrintable(caseterm, renaming)));
      return false;
    }
    Term notcaseterm = TheoryFactory.notSymbol.apply(caseterm);
    ret.add(new ExtraInfo(TermFactory.createEmptySubstitution(), caseterm, renaming));
    ret.add(new ExtraInfo(TermFactory.createEmptySubstitution(), notcaseterm, renaming));
    return true;
  }

  /**
   * Helper function for createStep: given that caseterm is an integer, this checks whether it is a
   * theory expression, and if so, updates ret with the cases caseterm < 0, caseterm = 0 and
   * caseterm > 0.  If not, then an appropriate error message is printed and false is returned.
   */
  private static boolean createIntegerCases(Term caseterm, Renaming renaming,
                                            Optional<OutputModule> module,
                                            ArrayList<ExtraInfo> ret) {
    if (!caseterm.isTheoryTerm() || !caseterm.isFirstOrder()) {
      module.ifPresent(o -> o.println("Cannot do case analysis on %a: this is an integer term, " +
        "but not a first-order theory term, so it cannot be included in the constraint.",
        Printer.makePrintable(caseterm, renaming)));
      return false;
    }
    Term zero = TheoryFactory.zeroValue;
    Term greater = TermFactory.createApp(TheoryFactory.greaterSymbol, caseterm, zero);
    Term equal = TermFactory.createApp(TheoryFactory.intEqualSymbol, caseterm, zero);
    Term smaller = TermFactory.createApp(TheoryFactory.smallerSymbol, caseterm, zero);
    Substitution empty = TermFactory.createEmptySubstitution();
    ret.add(new ExtraInfo(empty, greater, renaming));
    ret.add(new ExtraInfo(empty, equal, renaming));
    ret.add(new ExtraInfo(empty, smaller, renaming));
    return true;
  }

  /**
   * Helper function for createStep: this checks if the given caseterm is a variable of a
   * non-theory base type, or a tuple type.  If so, true is returned.  If not, false is
   * returned and an appropriate failure message printed to the given output module.
   */
  private static boolean nonTheoryCasesApplicable(Term caseterm, Renaming renaming,
                                                  Optional<OutputModule> module) {
    if (!caseterm.isVariable()) {
      module.ifPresent(o -> o.println("Cannot do a case analysis on %a: this term is not a " +
        "constraint or integer theory term, nor a variable (it has type %a).",
        Printer.makePrintable(caseterm, renaming), caseterm.queryType()));
      return false;
    }
    if (caseterm.queryType().isProductType()) return true;
    if (caseterm.queryType().isTheoryType()) {
      module.ifPresent(o -> o.println("Cannot do a case analysis on a variable of type %a.",
        caseterm.queryType()));
      return false;
    }
    return true;
  }

  /**
   * Helper function for createStep: given that caseterm is a non-theory non-array-type variable,
   * this considers all possible constructor instantiations.
   */
  private static void createConstructorCases(Variable caseterm, Renaming renaming,
                                             ProofContext pcontext,
                                             ArrayList<ExtraInfo> ret) {
    Set<FunctionSymbol> constructors = pcontext.getConstructors(caseterm.queryType());
    for (FunctionSymbol c : constructors) {
      MutableRenaming ren = renaming.copy();
      Type t = c.queryType();
      ArrayList<Term> args = new ArrayList<Term>(t.queryArity());
      while (t.isArrowType()) {
        Variable x = pcontext.getVariableNamer().chooseDerivative(caseterm, ren, t.subtype(1));
        args.add(x);
        t = t.subtype(2);
      }
      Substitution subst = TermFactory.createEmptySubstitution();
      subst.extend(caseterm, c.apply(args));
      ret.add(new ExtraInfo(subst, TheoryFactory.trueValue, ren));
    }
  }

  /**
   * Helper function for createStep: given that caseterm is a variable of product type, this
   * adds the instantiation by a tuple to the return list ret.
   * 
   * Note that this adds the new variables to the given renaming, and uses this same Renaming in
   * ExtraInfo.
   */
  private static void createTupleCase(Variable caseterm, Renaming renaming,
                                      ProofContext pcontext,
                                      ArrayList<ExtraInfo> ret) {
    Type type = caseterm.queryType();
    int n = type.numberSubtypes();
    ArrayList<Term> parts = new ArrayList<Term>(n);
    MutableRenaming ren = renaming.copy();
    for (int i = 1; i <= n; i++) {
      Type sub = type.subtype(i);
      Variable x = pcontext.getVariableNamer().chooseDerivative(caseterm, ren, sub);
      parts.add(x);
    }
    Substitution subst = TermFactory.createEmptySubstitution();
    subst.extend(caseterm, TermFactory.createTuple(parts));
    ret.add(new ExtraInfo(subst, TheoryFactory.trueValue, ren));
  }

  /**
   * The verification step ensures that the term we are doing a case analysis on actually uses only
   * variables that already occur in the equation.
   */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    Renaming renaming = _state.getTopEquation().getRenaming();
    for (Replaceable x : _term.freeReplaceables()) {
      if (renaming.getName(x) == null) {
        if (x == _term) {
          module.ifPresent(o -> o.println("Cannot do a case analysis on a variable that does " +
            "not occur in the equation."));
        }
        else {
          module.ifPresent(o -> o.println("Unknown %avariable in case term: \"%a\".",
            x.queryReplaceableKind() == Replaceable.Kind.METAVAR ? "meta-" : "", _term));
        }
        return false;
      }
    }
    return true;
  }

  /** Apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    EquationContext ec = _state.getTopEquation();
    ArrayList<EquationContext> replacements = new ArrayList<EquationContext>();
    int index = _state.getLastUsedIndex() + 1;
    for (ExtraInfo info : _cases) {
      Optional<Term> leftGeq = ec.getLeftGreaterTerm();
      Optional<Term> rightGeq = ec.getRightGreaterTerm();
      if (!leftGeq.isEmpty()) leftGeq = Optional.of(leftGeq.get().substitute(info.subst()));
      if (!rightGeq.isEmpty()) rightGeq = Optional.of(rightGeq.get().substitute(info.subst()));
      Term lhs = ec.getEquation().getLhs().substitute(info.subst());
      Term rhs = ec.getEquation().getRhs().substitute(info.subst());
      Term constraint = ec.getEquation().getConstraint().substitute(info.subst());
      constraint = TheoryFactory.createConjunction(constraint, info.constraint());
      replacements.add(new EquationContext(leftGeq, new Equation(lhs, rhs, constraint),
        rightGeq, index, info.renaming()));
      index++;
    }
    return _state.replaceTopEquation(replacements);
  }

  @Override
  public String commandDescription() {
    Renaming renaming = _state.getTopEquation().getRenaming();
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("case ", printer.makePrintable(_term, renaming));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    String applyonwhat = "the instance of";
    Renaming renaming = _state.getTopEquation().getRenaming();
    if (_term.queryType().equals(TypeFactory.boolSort)) applyonwhat = "the constraint";
    else if (_term.queryType().equals(TypeFactory.intSort)) applyonwhat = "the value of";
    module.println("We apply CASE on %a %a.", applyonwhat,
      Printer.makePrintable(_term, renaming));
  }
}

