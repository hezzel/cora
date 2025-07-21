/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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

import java.util.*;
import java.util.function.Function;
import charlie.util.FixedList;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.terms.Term;
import charlie.terms.FunctionSymbol;
import charlie.terms.Renaming;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.util.Pair;

/**
 * A ProofContext object keeps track of the fixed data in a proof, such as the underlying TRS and
 * rules.  It is an immutable object by nature.
 */
public class ProofContext {
  private final TRS _trs;
  private final ArrayList<String> _ruleNames = new ArrayList<String>();
  private final ArrayList<Renaming> _ruleRenamings = new ArrayList<Renaming>();
  private final HashMap<String,Integer> _nameToRule = new HashMap<String,Integer>();
  private final HashMap<Type,Set<FunctionSymbol>> _constructors =
    new HashMap<Type,Set<FunctionSymbol>>();
  private final HashMap<FunctionSymbol,Integer> _arities = new HashMap<FunctionSymbol,Integer>();
  private VariableNamer _namer = new VariableNamer();

  /**
   * Constructor: sets up a ProofContext with rules taken from the given TRS.
   * The TermPrinter is used for generating Renamings.
   */
  public ProofContext(TRS initialSystem, Function<List<Term>,Renaming> renamingMaker) {
    if (initialSystem == null) throw new NullStorageException("ProofContext", "initial TRS");
    _trs = initialSystem;
    int n = initialSystem.queryRuleCount();
    createRuleInfo(renamingMaker);
    createConstructorInfo();
  }

  /**
   * Helper function for the constructor: this names all the rules in the TRS, and generates a
   * Renaming for each of them.
   */
  private void createRuleInfo(Function<List<Term>,Renaming> renamingMaker) {
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      Rule rule = _trs.queryRule(i);
      Renaming renaming = renamingMaker.apply(List.of(
        rule.queryLeftSide(), rule.queryRightSide(), rule.queryConstraint()));
      String name = "O" + (i+1);
      _ruleNames.add(name);
      _nameToRule.put(name, i);
      _ruleRenamings.add(renaming);
      if (rule.queryLeftSide().isFunctionalTerm()) {
        FunctionSymbol f = rule.queryLeftSide().queryRoot();
        if (!_arities.containsKey(f)) _arities.put(f, rule.queryLeftSide().numberArguments());
      }
    }
  }

  /** Helper function for the constructor: this groups constructor symbols by their output type. */
  private void createConstructorInfo() {
    for (FunctionSymbol f : _trs.queryAlphabet().getSymbols()) {
      if (_trs.isDefined(f)) continue;
      if (f.isTheorySymbol()) continue;
      Type t = f.queryType().queryOutputType();
      Set<FunctionSymbol> set = _constructors.get(t);
      if (set == null) {
        set = new TreeSet<FunctionSymbol>();
        _constructors.put(t, set);
      }
      set.add(f);
    }
    for (Type t : _constructors.keySet()) {
      _constructors.put(t, Collections.unmodifiableSet(_constructors.get(t)));
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

  /** This gives the actual renaming for the rule.  Do not modify! */
  public Renaming getRenaming(String ruleName) {
    Integer i = _nameToRule.get(ruleName);
    if (i == null) return null;
    return _ruleRenamings.get(i);
  }

  /**
   * This returns the constructors with the give type as output type.  Note that this is the
   * FINAL output type, so if type is an arrow type, the empty set will be returned.
   *
   * Note also that the set is unmodifiable.
   */
  public Set<FunctionSymbol> getConstructors(Type type) {
    Set<FunctionSymbol> ret = _constructors.get(type);
    if (ret == null) return Set.of();
    return ret;
  }

  /**
   * This returns the arity of the given function symbol in the underlying TRS.  This assumes that
   * the function symbol has a consistent arity; if not, any of the possible arities may be returned
   * (but note that a consistent arity is a requirement for the application of rewriting induction).
   *
   * For constructors, we return 1 more than the constructor's arity.  For calculation symbols, we
   * return the symbol's arity.
   */
  public int queryRuleArity(FunctionSymbol symbol) {
    if (_arities.containsKey(symbol)) return _arities.get(symbol);
    if (symbol.isTheorySymbol() && !symbol.isValue()) return symbol.queryArity();
    return symbol.queryArity() + 1;
  }

  /** This returns a class for deduction rules to consistently name their variables. */
  public VariableNamer getVariableNamer() {
    return _namer;
  }
}

