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

import java.util.ArrayList;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.terms.Substitution;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.io.ParseableTermPrinter;
import cora.rwinduction.engine.*;

public final class ClauseDelete extends DeductionRule {
  public ClauseDelete(PartialProof proof, OutputModule module) { super(proof, module); }
  public ClauseDelete(PartialProof proof) { super(proof); }

  /** Try to apply the deduction rule to the current proof state */
  public boolean apply() {
    StepDelete step = createStep();
    if (!doChecks(step)) return false;
    return applyStep(step);
  }

  /** Create a step without doing all the necessary checks */
  StepDelete createStep() {
    Equation eq = _proof.getProofState().getTopEquation();
    // option 1: both sides are equal
    if (eq.getLhs().equals(eq.getRhs())) return new StepDelete(eq.getName(), true);
    // option 2: we will have to check the constraint
    else return new StepDelete(eq.getName(), false);
  }

  /** Do all the checks required before executing a step */
  private boolean doChecks(StepDelete step) {
    if (step == null) return false;
    if (step._bothSidesEqual) return true; // nothing to check
    Equation eq = _proof.getProofState().getTopEquation();
    switch (TermAnalyser.satisfy(eq.getConstraint(), Settings.smtSolver)) {
      case TermAnalyser.Result.MAYBE(String reason):
        explainFailure(reason);
        return false;
      case TermAnalyser.Result.YES(Substitution val):
        explainFailure(eq, val);
        return false;
      case TermAnalyser.Result.NO():
        return true;
    }
  }
  
  /** The SMT solver isn't sure whether the constraint is satisfiable: this prints the reason. */
  private void explainFailure(String explanation) {
    println("The DELETE rule is not obviously applicable: the left- and right-hand side " +
      "are not the same, and checking satisfiability returns MAYBE (%a)", explanation);
  }

  /** The SMT solver found a substitution that satisfies the constraint: print it. */
  private void explainFailure(Equation equation, Substitution subst) {
    println("The DELETE rule is not applicable: the left- and right-hand side are not " +
      "the same, and the constraint is satisfiable using substitution %a.",
      new Pair<Substitution,Renaming>(subst, equation.getRenaming()));
  }

  /** The DeductionStep instance returned by this deduction rule */
  private class StepDelete extends DeductionStep {
    private String _equationName;
    private boolean _bothSidesEqual;
  
    StepDelete(String equation, boolean equalsides) {
      _equationName = equation;
      _bothSidesEqual = equalsides;
    }
  
    /** Applying the step deletes the top equation. */
    public ProofState applyIgnoreExceptions(PartialProof proof) {
      return proof.getProofState().deleteTopEquation();
    }
  
    public String commandDescription(ParseableTermPrinter printer) {
      return "delete";
    }
  
    public void explain(OutputModule module) {
      module.println("We apply DELETION to %a because %a.  " +
        "Thus, we may remove this equation from the proof state.", _equationName,
        _bothSidesEqual ? "both sides are equal" : "the constraint is unsatisfiable");
    }
  }
}

