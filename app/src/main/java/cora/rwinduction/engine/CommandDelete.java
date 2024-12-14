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

package cora.rwinduction.engine;

import java.util.ArrayList;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.terms.Substitution;
import charlie.theorytranslation.TermAnalyser;
import cora.config.Settings;
import cora.io.OutputModule;

public final class CommandDelete implements Command {
  public void run(PartialProof proof, OutputModule module) {
    Equation eq = proof.getProofState().getTopEquation();
    boolean ok = false;
    if (eq.getLhs().equals(eq.getRhs())) ok = true;
    else {
      TermAnalyser.Result res = TermAnalyser.satisfy(eq.getConstraint(), Settings.smtSolver);
      ok = switch (res) {
        case TermAnalyser.Result.NO() -> true;
        case TermAnalyser.Result.MAYBE(String reason) -> { explain(reason, module); yield false; }
        case TermAnalyser.Result.YES(Substitution val) -> { explain(eq, val, module); yield false; }
      };
    }
    if (ok) {
      ProofState state = proof.getProofState().deleteTopEquation();
      proof.addProofStep(state, "delete");
    }
  }

  /** The SMT solver isn't sure whether the constraint is satisfiable: this prints the reason. */
  private void explain(String explanation, OutputModule module) {
    module.println("The DELETE rule is not obviously applicable: the left- and right-hand side " +
      "are not the same, and checking satisfiability returns MAYBE (%a)", explanation);
  }

  /** The SMT solver found a substitution that satisfies the constraint: print it. */
  private void explain(Equation equation, Substitution subst, OutputModule module) {
    Renaming renaming = equation.getRenaming();
    StringBuilder desc = new StringBuilder("[");
    ArrayList<Object> args = new ArrayList<Object>();
    boolean first = true;
    for (Variable x : equation.getConstraint().vars()) {
      if (first) first = false;
      else desc.append(", ");
      desc.append("%a:=%a");
      args.add(renaming.getName(x));
      args.add(new Pair<Term,Renaming>(subst.getReplacement(x), renaming));
    }
    desc.append("]");
    module.println("The DELETE rule is not applicable: the left- and right-hand side are not " +
      "the same, and the constraint is satisfiable using substitution %a.",
      new Pair<String,Object[]>(desc.toString(), args.toArray()));
  }
}
