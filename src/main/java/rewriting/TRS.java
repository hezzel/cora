/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

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
import cora.terms.Position;

/**
 * A TRS (term rewriting system) is an abstract rewriting system based on a set of rules.
 * It is key to rewriting, and it is that which we analyse for various properties.
 *
 * There are many kinds of term rewriting systems, with different restrictions on rule and term
 * formation.  Hence, this is an abstract class; most techniques will wish to deal with specific
 * instances, such as many-sorted TRSs or higher-order LCTRSs.
 *
 * We do impose the limitation that the set of rules for a TRS is finite.  However, since a "Rule"
 * can also be a rule scheme, this seems reasonable.
 */
public abstract class TRS {
  private Alphabet _alphabet;
  private List<Rule> _rules;

  /** Create a TRS with the given alphabet and rules. */
  protected TRS(Alphabet alphabet, List<Rule> rules) {
    if (alphabet == null) throw new NullInitialisationError("TRS", "alphabet");
    if (rules == null) throw new NullInitialisationError("TRS", "rules set");
    for (int i = 0; i < rules.size(); i++) {
      if (rules.get(i) == null) throw new NullInitialisationError("TRS", "rule " + i); 
    }   

    _alphabet = alphabet.copy();
    _rules = new ArrayList<Rule>(rules);
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

  /**
   * Returns the FunctionSymbol associated to the given name in this TRS, if there is a unique
   * one.
   */
  public FunctionSymbol lookupSymbol(String name) {
    return _alphabet.lookup(name);
  }

  /**
   * Returns the leftmost, innermost position where a rule may be applied, or null if no such
   * position exists.
   */
  public Position leftmostInnermostRedexPosition(Term s) {
    List<Position> positions = s.queryAllPositions();
    for (int i = 0; i < positions.size(); i++) {
      Position pos = positions.get(i);
      Term sub = s.querySubterm(pos);
      for (int j = 0; j < _rules.size(); j++) {
        if (_rules.get(j).applicable(sub)) return pos;
      }
    }
    return null;
  }

  /**
   * Reduces the given term at the leftmost, innermost redex position, and returns the result;
   * if no such position exists, null is returned instead.
   * If multiple rules match, an arbitrary one is chosen.
   */
  public Term leftmostInnermostReduce(Term s) {
    List<Rule> tmp = new ArrayList<Rule>(_rules);
    Collections.shuffle(tmp);
    Position pos = leftmostInnermostRedexPosition(s);
    if (pos == null) return null;
    Term subterm = s.querySubterm(pos);
    for (int j = 0; j < tmp.size(); j++) {
      Term result = tmp.get(j).apply(subterm);
      if (result != null) return s.replaceSubterm(pos, result);
    }
    return null;
  }


  /** Gives a human-readable representation of the term rewriting system. */
  public String toString() {
    String ret = _alphabet.toString() + "\n";
    for (int i = 0; i < _rules.size(); i++) {
      ret += _rules.get(i).toString() + "\n";
    }
    return ret;
  }
}

