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
import java.util.Stack;
import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/** This deduction step handles the "generalise drop <constraint>" command syntax. */
public final class DeductionGeneraliseDrop extends DeductionStep {
  private Term _newConstraint;
  private Term _dropped;

  private DeductionGeneraliseDrop(ProofState state, ProofContext context,
                                  Term newconstr, Term dropped) {
    super(state, context);
    _newConstraint = newconstr;
    _dropped = dropped;
  }

  /**
   * Helper function for createStep: this splits up a constraint φ1 ∧...∧ φn into its separate
   * components φi, which are themselves not conjunctions.
   */
  private static ArrayList<Term> split(Term constraint) {
    ArrayList<Term> ret = new ArrayList<Term>();
    Stack<Term> todo = new Stack<Term>();
    todo.push(constraint);
    while (!todo.isEmpty()) {
      Term term = todo.pop();
      while (term.isFunctionalTerm() && term.queryRoot().equals(TheoryFactory.andSymbol) &&
             term.numberArguments() == 2) {
        todo.push(term.queryArgument(2));
        term = term.queryArgument(1);
      }
      ret.add(term);
    }
    return ret;
  }

  public static DeductionGeneraliseDrop createStep(PartialProof proof,
                                                  Optional<OutputModule> module, Term dropme) {
    ProofState state = proof.getProofState();
    Equation eq = getTopEquation(state, module);
    if (eq == null) return null;
    ArrayList<Term> originalComponents = split(eq.getConstraint());
    ArrayList<Term> remove = split(dropme);
    for (Term todrop : remove) {
      boolean found = false;
      for (int i = 0; i < originalComponents.size() && !found; i++) {
        if (originalComponents.get(i) != null && originalComponents.get(i).equals(todrop)) {
          originalComponents.set(i, null);
          found = true;
        }
      }
      if (!found) {
        module.ifPresent(o -> o.println("No such subterm in the constraint: %a.",
          Printer.makePrintable(todrop, state.getTopEquation().getRenaming())));
        return null;
      }
    }
    Term updated = TheoryFactory.trueValue;
    for (Term component : originalComponents) {
      if (component != null) updated = TheoryFactory.createConjunction(updated, component);
    }
    return new DeductionGeneraliseDrop(state, proof.getContext(), updated, dropme);
  }

  /** There's nothing to check; we can always generalise in this way. */
  @Override
  public boolean verify(Optional<OutputModule> module) {
    return true;
  }

  /** Apply the deduction rule to the current proof state */
  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    Equation oldEquation = _state.getTopEquation().getEquation();
    Equation newEquation = new Equation(oldEquation.getLhs(), oldEquation.getRhs(), _newConstraint);
    int newIndex = _state.getLastUsedIndex()+1;
    return _state.replaceTopEquation(_state.getTopEquation().replace(newEquation, newIndex))
                 .setIncomplete(newIndex);
  }

  @Override
  public String commandDescription() {
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("generalise drop");
    printer.add(printer.makePrintable(_dropped, _state.getTopEquation().getRenaming()));
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    module.println("We apply GENERALISE to replace the constraint of %a by %a.",
      _equ.getName(), Printer.makePrintable(_newConstraint, _state.getTopEquation().getRenaming()));
  }
}

