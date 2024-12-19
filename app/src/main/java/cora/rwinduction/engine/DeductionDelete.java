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

public final class DeductionDelete extends DeductionRule {
  public DeductionDelete(PartialProof proof, OutputModule module) { super(proof, module); }
  public DeductionDelete(PartialProof proof) { super(proof); }
  
  public boolean apply() {
    Equation eq = _proof.getProofState().getTopEquation();
    // if lhs = rhs we may do the proof step regardless of the constraint
    if (!eq.getLhs().equals(eq.getRhs())) {
      TermAnalyser.Result res = TermAnalyser.satisfy(eq.getConstraint(), Settings.smtSolver);
      switch (res) {
        case TermAnalyser.Result.MAYBE(String reason):
          if (_module != null) explain(reason);
          return false;
        case TermAnalyser.Result.YES(Substitution val):
          if (_module != null) explain(eq, val);
          return false;
        case TermAnalyser.Result.NO(): break;
      }
    }
    ProofState state = _proof.getProofState().deleteTopEquation();
    _proof.addProofStep(state, "delete");
    return true;
  }

  /** The SMT solver isn't sure whether the constraint is satisfiable: this prints the reason. */
  private void explain(String explanation) {
    _module.println("The DELETE rule is not obviously applicable: the left- and right-hand side " +
      "are not the same, and checking satisfiability returns MAYBE (%a)", explanation);
  }

  /** The SMT solver found a substitution that satisfies the constraint: print it. */
  private void explain(Equation equation, Substitution subst) {
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
    _module.println("The DELETE rule is not applicable: the left- and right-hand side are not " +
      "the same, and the constraint is satisfiable using substitution %a.",
      new Pair<String,Object[]>(desc.toString(), args.toArray()));
  }
}
