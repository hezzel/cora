/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rewriting;

import java.util.List;
import java.util.ArrayList;
import java.util.TreeMap;
import java.util.Collections;
import cora.exceptions.IndexingError;
import cora.exceptions.NullInitialisationError;
import cora.terms.FunctionSymbol;
import cora.terms.Term;
import cora.terms.Path;

/**
 * A TRS (term rewriting system) is an abstract rewriting system based on a (possibly infinite)
 * set of rules and a set of rule schemes.
 * It is key to rewriting, and it is that which we analyse for various properties.
 *
 * To be able to analyse TRSs, we impose the limitation that the rules can be expressed as a finite
 * number of standard rules (which are allowed to be constrained), and a finite number of rule
 * schemes, where the latter essentially generates a countable number of rules.  For now, we limit
 * interest to beta, eta and calc as rule schemes, so techniques know how to deal with this.
 *
 * To be able to deal with the constraints and calculation rules, the TRS internally tracks whether
 * or not it supports a theory.  For now, we do not keep track of *which* theories the TRS supports;
 * any TRS that supports theories is expected to support all the theories implemented in Cora.
 */
public class TRS {
  private Alphabet _alphabet;
  private List<Rule> _rules;
  private List<Scheme> _schemes;
  private boolean _theories;

  /**
   * Create a TRS with the given alphabet, rules and rule schemes.  Default because this should
   * only be called by the factory, which also does the correctness checking (such as making sure
   * that none of the components are null, and that the lists are not used elsewhere.
   */
  TRS(Alphabet alphabet, List<Rule> rules, List<Scheme> schemes, boolean constrained) {
    _alphabet = alphabet;
    _rules = rules;
    _schemes = schemes;
    _theories = constrained;
  }

  /** @return the number of rules in the TRS that can be queried. */
  public int queryRuleCount() {
    return _rules.size();
  }

  /** For 0 <= index < queryRuleCount(), this returns one of the rules in the system. */
  public Rule queryRule(int index) {
    if (index < 0 || index >= queryRuleCount()) {
      throw new IndexingError("TRS", "queryRule", index, 0, queryRuleCount()-1);
    }
    return _rules.get(index);
  }

  /** @return the number of schemes in the TRS that can be queried. */
  public int querySchemeCount() {
    return _schemes.size();
  }

  /** For 0 ≤ index < querySchemeCount(), this returns one of the schemes in the system. */
  public Scheme queryScheme(int index) {
    if (index < 0 || index >= querySchemeCount()) {
      throw new IndexingError("TRS", "queryScheme", index, 0, querySchemeCount()-1);
    }
    return _schemes.get(index);
  }

  /**
   * Returns the FunctionSymbol associated to the given name in this TRS, if there is a unique
   * one.  This does not include theory symbols since these are allowed to be polymorphic!
   */
  public FunctionSymbol lookupSymbol(String name) {
    return _alphabet.lookup(name);
  }

  /** Returns whether theory symbols and logical constraints are supported. */
  public boolean isConstrained() {
    return _theories;
  }

  /**
   * Returns the leftmost, innermost position where a rule or scheme may be applied, or null if no
   * such position exists.
   */
  public Path leftmostInnermostRedexPosition(Term s) {
    List<Path> positions = s.queryPositions();
    for (int i = 0; i < positions.size(); i++) {
      Path pos = positions.get(i);
      Term sub = pos.queryCorrespondingSubterm();
      for (int j = 0; j < _rules.size(); j++) {
        if (_rules.get(j).applicable(sub)) return pos;
      }
      for (int j = 0; j < _schemes.size(); j++) {
        if (_schemes.get(j).applicable(sub)) return pos;
      }
    }
    return null;
  }

  private class RuleOrScheme {
    boolean rule;
    int index;
    public RuleOrScheme(boolean r, int i) { rule = r; index = i; }
  }

  /**
   * Reduces the given term at the leftmost, innermost redex position, and returns the result;
   * if no such position exists, null is returned instead.
   * If multiple rules or schemes match, an arbitrary one is chosen.
   */
  public Term leftmostInnermostReduce(Term s) {
    Path pos = leftmostInnermostRedexPosition(s);
    if (pos == null) return null;

    // get a shuffled list of all the rules and schemes
    ArrayList<RuleOrScheme> lst = new ArrayList<RuleOrScheme>();
    for (int i = 0; i < _rules.size(); i++) lst.add(new RuleOrScheme(true, i));
    for (int i = 0; i < _schemes.size(); i++) lst.add(new RuleOrScheme(false, i));
    Collections.shuffle(lst);
    
    Term subterm = pos.queryCorrespondingSubterm();
    for (int i = 0; i < lst.size(); i++) {
      Term result;
      if (lst.get(i).rule) result = _rules.get(lst.get(i).index).apply(subterm);
      else result = _schemes.get(lst.get(i).index).apply(subterm);
      if (result != null) return s.replaceSubterm(pos, result);
    }

    return null;
  }

  /** Gives a human-readable representation of the term rewriting system. */
  public String toString() {
    StringBuilder ret = new StringBuilder();
    ret.append(_alphabet.toString());
    ret.append("\n");
    if (_theories) {
      ret.append("All the standard theory symbols are also included.\n");
    }
    for (int i = 0; i < _rules.size(); i++) {
      ret.append(_rules.get(i).toString());
      ret.append("\n");
    }
    for (int i = 0; i < _schemes.size(); i++) {
      ret.append(_schemes.get(i).toString());
      ret.append("\n");
    }
    return ret.toString();
  }
}

