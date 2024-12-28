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

import java.util.TreeSet;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.terms.Replaceable;
import charlie.terms.Substitution;
import charlie.trs.Rule;
import cora.io.OutputModule;
import cora.io.ParseableTermPrinter;
import cora.rwinduction.engine.*;

public class StepSimplify extends DeductionStep {
  private Equation _equation;
  private Rule _rule;
  private EquationPosition _position;
  private Substitution _substitution;
  private String _ruleName;
  private Renaming _ruleRenaming;
  private Renaming _equationRenaming;

  StepSimplify(Equation equation, Rule rule, EquationPosition pos, Substitution subst,
               String ruleName, Renaming ruleRenaming) {
    _equation = equation;
    _rule = rule;
    _position = pos;
    _substitution = subst;
    _ruleName = ruleName;
    _ruleRenaming = ruleRenaming;
  }

  public Rule getRule() { return _rule; }
  public Equation getEquation() { return _equation; }
  public Renaming getRuleRenaming() { return _ruleRenaming; }
  public Substitution getSubstitution() { return _substitution; }

  public ProofState applyIgnoreExceptions(PartialProof proof) {
    Term substituted = _rule.queryRightSide().substitute(_substitution);
    Equation replaced = _equation.replaceSubterm(_position, substituted,
      proof.getFirstAvailableIndex());
    return proof.getProofState().replaceTopEquation(replaced);
  }

  public String commandDescription(ParseableTermPrinter printer) {
    StringBuilder substitutionString = new StringBuilder("[");
    TreeSet<Replaceable> keys = new TreeSet<Replaceable>(_substitution.domain());
    boolean first = true;
    for (Replaceable x : keys) {
      if (first) first = false;
      else substitutionString.append("; ");
      substitutionString.append(_ruleRenaming.getName(x));
      substitutionString.append(" := ");
      printer.print(_substitution.get(x), _equation.getRenaming(), substitutionString);
    }
    substitutionString.append("]");
    return "simplify " + _ruleName + " " + _position.toString() +
      " with " + substitutionString.toString();
  }

  public void explain(OutputModule module) {
    Pair<Renaming,Renaming> renamings =
      new Pair<Renaming,Renaming>(_ruleRenaming, _equation.getRenaming());
    Pair<Substitution,Pair<Renaming,Renaming>> substitutionInfo =
      new Pair<Substitution,Pair<Renaming,Renaming>>(_substitution, renamings);
    module.println("We apply SIMPLIFICATION to %a with rule %a and substitution %a.",
      _equation.getName(), _ruleName, substitutionInfo);
  }
}

