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
import java.util.HashMap;
import java.util.Stack;
import charlie.exceptions.NullStorageException;
import charlie.util.FixedList;
import charlie.terms.Renaming;
import charlie.terms.TermPrinter;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.printer.ParseableTermPrinter;
import charlie.util.Pair;
import cora.io.OutputModule;

/**
 * A ProofContext object keeps track of the fixed data in a proof, such as the underlying TRS and
 * rules.  It is an immutable object by nature.
 */
public class ProofContext {
  private final TRS _trs;
  private final ArrayList<String> _ruleNames = new ArrayList<String>();
  private final ArrayList<Renaming> _ruleRenamings = new ArrayList<Renaming>();
  private final HashMap<String,Integer> _nameToRule = new HashMap<String,Integer>();

  /**
   * Constructor: sets up a ProofContext with rules taken from the given TRS.
   * The TermPrinter is used for generating Renamings.
   */
  public ProofContext(TRS initialSystem, TermPrinter tp) {
    if (initialSystem == null) throw new NullStorageException("ProofContext", "initial TRS");
    _trs = initialSystem;
    int n = initialSystem.queryRuleCount();
    for (int i = 0; i < initialSystem.queryRuleCount(); i++) {
      Rule rule = initialSystem.queryRule(i);
      Renaming renaming =
        tp.generateUniqueNaming(rule.queryLeftSide(), rule.queryRightSide(), rule.queryConstraint());
      String name = "O" + (i+1);
      _ruleNames.add(name);
      _nameToRule.put(name, i);
      _ruleRenamings.add(renaming);
    }
  }

  public TRS getTRS() {
    return _trs;
  }

  public String getRuleName(int index) {
    return _ruleNames.get(index);
  }

  public boolean hasRule(String name) {
    return _nameToRule.containsKey(name);
  }

  public Rule getRule(String name) {
    Integer i = _nameToRule.get(name);
    if (i == null) return null;
    return _trs.queryRule(i);
  }

  public Renaming getRenaming(String ruleName) {
    Integer i = _nameToRule.get(ruleName);
    if (i == null) return null;
    return _ruleRenamings.get(i);
  }
}

