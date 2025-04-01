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
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.terms.TheoryFactory;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * The variant of Alter that is only used to add definitions x = t to the constraint, where x is a
 * fresh variable, and t contains only variables that occur at a prior place in the equation.
 */
public final class DeductionAlterDefinitions extends DeductionStep {
  private ArrayList<Term> _definitions;
  private Renaming _updatedRenaming;

  /** Creates the step, claiming both arguments as its own property. */
  private DeductionAlterDefinitions(ProofState state, ProofContext context,
                                    ArrayList<Term> defs, Renaming naming) {
    super(state, context);
    _definitions = defs;
    _updatedRenaming = naming;
  }

  /**
   * Creates a step to add the given definitions to the top equation's constraint.
   * This will only work if each variable is fresh, and each term uses only variables that either
   * already occur in the equation (and have a theory sort), of that occur previously in the
   * definition list.
   */
  public static Optional<DeductionAlterDefinitions> createStep(PartialProof proof,
                                                      Optional<OutputModule> module,
                                                      ArrayList<Pair<Variable,Term>> defs) {
    ProofState state = proof.getProofState();
    Equation eq = getTopEquation(state, module);
    Renaming renaming = state.getTopEquation().getRenaming();

    ArrayList<Term> d = new ArrayList<Term>();
    if (defs.size() == 0) {
      module.ifPresent(o -> o.println("Cannot introduce an empty number of definitions."));
      return Optional.empty();
    }
    for (Pair<Variable,Term> pair : defs) {
      Variable x = pair.fst();
      Term value = pair.snd();
      if (!checkMapping(x, value, renaming, module)) return Optional.empty();
      String name = x.queryName();
      for (int i = 1; !renaming.setName(x, name); i++) name = x.queryName() + i;
      d.add(TheoryFactory.createEquality(x, value));
    }

    return Optional.of(new DeductionAlterDefinitions(state, proof.getContext(), d, renaming));
  }

  /**
   * This checks if we are allowed to add the given equality x = value, given that the known
   * variables in the equation context so far are all in the given renaming.
   */
  private static boolean checkMapping(Variable x, Term value, Renaming renaming,
                                      Optional<OutputModule> module) {
    // the variable should be fresh
    if (renaming.getName(x) != null) {
      module.ifPresent(o -> o.println("Definition for variable [%a] not allowed: this variable " +
        "already occurs in the equation context.", x.queryName()));
      return false;
    }
    // the variable must be a theory variable
    if (!x.queryType().isBaseType() || !x.queryType().isTheoryType()) {
      module.ifPresent(o -> o.println("Variable %a has type %a, which is not a theory sort.",
        x.queryName(), x.queryType()));
      return false;
    }
    // all the variables in value should be known
    for (Variable y : value.vars()) {
      if (renaming.getName(y) == null) {
        module.ifPresent(o -> o.println("Unknown variable %a in definition of %a.",
          y.queryName(), x.queryName()));
        return false;
      }
    }
    // the value should be a first-order theory term
    if (!value.isFirstOrder() || !value.isTheoryTerm()) {
      module.ifPresent(o -> o.println("Value %a is not a (first-order) theory term, so does not " +
        "belong in the constraint!", Printer.makePrintable(value, renaming)));
      return false;
    }
    // the variable and value must have the same type
    if (!x.queryType().equals(value.queryType())) {
      module.ifPresent(o -> o.println("Type error: variable %a has type %a while %a has type %a.",
        x.queryName(), x.queryType(), Printer.makePrintable(value, renaming), value.queryType()));
      return false;
    }
    // all good!
    return true;
  }

  /** There's nothing heavy to check: if we can create this step, we can execute it. */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    return true;
  }

  /** Apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Equation old = _state.getTopEquation().getEquation();
    Term constraint = old.getConstraint();
    for (Term def : _definitions) {
      constraint = TheoryFactory.createConjunction(constraint, def);
    }
    Equation equation = new Equation(old.getLhs(), old.getRhs(), constraint);
    return _state.replaceTopEquation(_state.getTopEquation().replace(equation,
      _updatedRenaming, _state.getLastUsedIndex() + 1));
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("alter add ");
    for (int i = 0; i < _definitions.size(); i++) {
      if (i != 0) printer.add(", ");
      printer.add(printer.makePrintable(_definitions.get(i).queryArgument(1), _updatedRenaming),
                  " = ",
                  printer.makePrintable(_definitions.get(i).queryArgument(2), _updatedRenaming));
    }
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    Term newConstraint = TheoryFactory.trueValue;
    for (Term c : _definitions) newConstraint = TheoryFactory.createConjunction(newConstraint, c);
    module.println("We apply ALTER to add %a to the constraint of %a.",
      newConstraint, _equ.getName());
  }
}

