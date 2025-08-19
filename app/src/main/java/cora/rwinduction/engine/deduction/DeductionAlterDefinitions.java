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
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
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
  private MutableRenaming _updatedRenaming;

  /** Creates the step, claiming both arguments as its own property. */
  private DeductionAlterDefinitions(ProofState state, ProofContext context,
                                    ArrayList<Term> defs, MutableRenaming naming) {
    super(state, context);
    _definitions = defs;
    _updatedRenaming = naming;
  }

  /**
   * This returns the renaming that will be used for the result of the step.
   * This renaming is the property of the current object, and may not be altered.
   */
  Renaming queryUpdatedRenaming() {
    return _updatedRenaming.makeImmutable();
  }

  /**
   * Creates a step to add the given definitions to the top equation's constraint.
   * This will only work if each variable is fresh, and each term uses only variables that either
   * already occur in the equation (and have a theory sort), of that occur previously in the
   * definition list.
   * (If it fails, null is returned.)
   */
  public static DeductionAlterDefinitions createStep(PartialProof proof,
                                                Optional<OutputModule> module,
                                                ArrayList<Pair<Pair<Variable,String>,Term>> defs) {
    ProofState state = proof.getProofState();
    Equation eq = getTopEquation(state, module);
    MutableRenaming renaming = state.getTopEquation().getRenamingCopy();

    ArrayList<Term> d = new ArrayList<Term>();
    if (defs.size() == 0) {
      module.ifPresent(o -> o.println("Cannot introduce an empty number of definitions."));
      return null;
    }
    for (var tuple : defs) {
      Variable x = tuple.fst().fst();
      String name = tuple.fst().snd();
      Term value = tuple.snd();
      if (!checkMapping(x, name, value, renaming, module)) return null;
      if (!renaming.setName(x, name)) {
        module.ifPresent(o -> o.println("Invalid variable name: " + name));
      }
      d.add(TheoryFactory.createEquality(x, value));
    }

    return new DeductionAlterDefinitions(state, proof.getContext(), d, renaming);
  }

  /**
   * This checks if we are allowed to add the given equality x = value, given that the known
   * variables in the equation context so far are all in the given renaming.
   */
  private static boolean checkMapping(Variable x, String xname, Term value, Renaming renaming,
                                      Optional<OutputModule> module) {
    // the variable should be fresh
    if (renaming.getName(x) != null) {
      module.ifPresent(o -> o.println("Definition for variable [%a] not allowed: this variable " +
        "already occurs in the equation context.", xname));
      return false;
    }
    // the name should be fresh, too
    if (renaming.getReplaceable(xname) != null) {
      module.ifPresent(o -> o.println("Definition for variable [%a] not allowed: this name has " +
        "already been used in the equation context.", xname));
      return false;
    }
    // the variable must be a theory variable
    if (!x.queryType().isBaseType() || !x.queryType().isTheoryType()) {
      module.ifPresent(o -> o.println("Variable %a has type %a, which is not a theory sort.",
        xname, x.queryType()));
      return false;
    }
    // all the variables in value should be known
    for (Variable y : value.vars()) {
      if (renaming.getName(y) == null) {
        module.ifPresent(o -> o.println("Unknown variable %a in definition of %a.",
          y.queryName(), xname));
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
        xname, x.queryType(), Printer.makePrintable(value, renaming), value.queryType()));
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

  /** This returns the constraint that is added to the main constraint. */
  public Term queryAddedConstraint() {
    Term constraint = TheoryFactory.trueValue;
    for (Term def : _definitions) constraint = TheoryFactory.createConjunction(constraint, def);
    return constraint;
  }

  /** This returns the updated constraint that will be the result of applying this rule. */
  public Term queryUpdatedConstraint() {
    Term constraint = _state.getTopEquation().getEquation().getConstraint();
    for (Term def : _definitions) constraint = TheoryFactory.createConjunction(constraint, def);
    return constraint;
  }

  /** Apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Equation old = _state.getTopEquation().getEquation();
    Term constraint = old.getConstraint();
    for (Term def : _definitions) constraint = TheoryFactory.createConjunction(constraint, def);
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
      Printer.makePrintable(newConstraint, _updatedRenaming), _equ.getName());
  }
}

