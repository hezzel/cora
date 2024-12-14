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
import charlie.util.FixedList;
import charlie.types.Type;
import charlie.types.Arrow;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

/** The environment command :rules, which prints all or a specific subset of rules to the user. */
public class CommandRules extends Command {
  public String queryName() {
    return ":rules";
  }

  public FixedList<String> callDescriptor() {
    return FixedList.of(":rules", ":rules <function symbol>");
  }

  public String helpDescriptor() {
    return "List all the rules available in the original TRS.  " +
           "You can also list only the rules with a specific root symbol.";
  }

  protected boolean run(String args) {
    if (args.indexOf(' ') != -1) return failure("Too many arguments: :rules takes 0 or 1");
    if (args.equals("")) { printAllMatchingRules(null); return true; }
    try {
      Term fterm = CoraInputReader.readTerm(args, _proof.getTRS());
      if (!fterm.isConstant()) {
        return failure("Argument to :rules should be a single function symbol");
      }
      printAllMatchingRules(fterm.queryRoot());
      printCalculationRule(fterm.queryRoot());
      return true;
    }
    catch (Exception e) { return failure(e.getMessage().trim()); }
  }

  /** Prints the normal rules (with the required start symbol) */
  private void printAllMatchingRules(FunctionSymbol start) {
    TRS trs = _proof.getTRS();
    boolean printed = false;
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      Rule rule = trs.queryRule(i);
      FunctionSymbol f = rule.queryRoot();
      if (start != null && f != null && !start.equals(f)) continue;
      if (!printed) { _module.startTable(); printed = true; }
      String name = _proof.getRuleName(i);
      Renaming renaming = _proof.getRenaming(name);
      _module.nextColumn("%a:", name);
      _module.println("%a", new Pair<Rule,Renaming>(rule, renaming));
    }
    if (printed) _module.endTable();
    else if (start == null) _module.println("This TRS has no rules.");
    else _module.println("There are no rules with " + start.toString() + " as root symbol.");
  }

  /** Helper function for run: prints a calculation rule with the required start symbol */
  private void printCalculationRule(FunctionSymbol start) {
    Term left = start == null ? null : start.toCalculationSymbol();
    if (left == null) return;         // nothing to do
    for (int i = 1; left.queryType() instanceof Arrow(Type in, Type out); i++) {
      left = left.apply(TermFactory.createVar("x" + i, in));
    }
    Term right = TermFactory.createVar("z", left.queryType());
    Term constraint = TheoryFactory.createEquality(right, left);
    _module.println("The calculation rule for this symbol is: %a %{ruleArrow} %a | %a .",
      left, right, constraint);
  }

}

