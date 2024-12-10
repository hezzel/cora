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

package cora.rwinduction.command;

import charlie.util.Pair;
import charlie.types.Arrow;
import charlie.types.Type;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import cora.io.OutputModule;
import cora.rwinduction.engine.ProverContext;

/**
 * The :rules command: it simply shows all the required rules, or the rules starting with the given
 * symbol.
 */
public class CmdMetaRules implements Command {
  private FunctionSymbol _startSymbol;

  /** The command :rules to just print all rules available to the user. */
  public CmdMetaRules() {
    _startSymbol = null;
  }

  /** The command :rules f, to print all rules starting with f. */
  public CmdMetaRules(FunctionSymbol f, String name) {
    _startSymbol = f;
  }

  /** Primarily for unit testing */
  public FunctionSymbol queryStartSymbol() {
    return _startSymbol;
  }

  /** Executes the command */
  public void run(ProverContext context, OutputModule module) {
    printAllMatchingRules(context, module);
    printCalculationRule(module);
  }

  /** Helper function for run: prints the normal rules (with the required start symbol) */
  private void printAllMatchingRules(ProverContext context, OutputModule module) {
    TRS trs = context.getTRS();
    boolean printed = false;
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rule = trs.queryRule(i);
      FunctionSymbol f = rule.queryRoot();
      if (_startSymbol != null && f != null && !_startSymbol.equals(f)) continue;
      if (!printed) { module.startTable(); printed = true; }
      String name = context.getRuleName(i);
      Renaming renaming = context.getRenaming(name);
      module.nextColumn("%a:", name);
      module.println("%a", new Pair<Rule,Renaming>(rule, renaming));
    }
    if (printed) module.endTable();
    else if (_startSymbol == null) module.println("This TRS has no rules.");
    else module.println("There are no rules with " + _startSymbol.toString() + " as root symbol.");
  }

  /** Helper function for run: prints a calculation rule with the required start symbol */
  private void printCalculationRule(OutputModule module) {
    if (_startSymbol == null) return; // nothing to do
    Term left = _startSymbol == null ? null : _startSymbol.toCalculationSymbol();
    if (left == null) return;         // nothing to do
    for (int i = 1; left.queryType() instanceof Arrow(Type in, Type out); i++) {
      left = left.apply(TermFactory.createVar("x" + i, in));
    }
    Term right = TermFactory.createVar("z", left.queryType());
    Term constraint = TheoryFactory.createEquality(right, left);
    module.println("The calculation rule for this symbol is: %a %{ruleArrow} %a | %a .",
      left, right, constraint);
  }
}

