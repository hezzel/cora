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

package cora.termination.dependency_pairs;

import charlie.exceptions.IndexingException;
import charlie.exceptions.NullStorageException;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.terms.FunctionSymbol;
import charlie.types.Type;
import charlie.types.TypeFactory;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

public class Problem {
  public enum TerminationFlag { Computable, Terminating, Arbitrary };
  private final List<DP> _dps;
  private final List<Rule> _rules;
  private final Set<Integer> _privateIndexes;
  private TRS _originalTrs;
  private boolean _innermost;
  private boolean _extraRules; 
  private TerminationFlag _terminationFlag;

  /**
   * Sets up a DP problem (these arguments cannot be changed).
   * @param dps The dependency pairs in this problem.
   * @param rules The rules in this problem.
   * @param privates The indexes of those dependency pairs (in the dps list) that should be
   *  considered "private", so may not be used as the first argument of a chain.
   *  If nothing is private, this is allowed to be null.
   * @param original The original TRS which this DP chain regards.  This is important for term
   *  formation and rule schemes, and moreover all instantiations of left-hand sides of dependency
   *  pairs are assumed to have arguments that are computable with respect to this original TRS.
   *  Moreover, if the innermost flag is set, then all instantiations of left-hand sides of DPs are
   *  expected to be in normal form with respect to this TRS.
   *  There is an important correctness property that people constructing a Problem should satisfy:
   *  any normal form with respect to original should also be a normal form with respect to rules.
   *  In addition, the alphabet for this TRS includes all symbols that occur in any DP (including
   *  the sharped symbols, which are constructors).
   *  Neither property is explicitly tested, but failing to comply with these rules will endanger
   *  soundness of the DP framework.
   * @param extraRules True if there are extra rules in the Problem that are not listed (as in
   *  universal computability; these rules must satisfy certain requirements, such as defining only
   *  symbols that do not occur in the original TRS or in rules).  False otherwise.
   * @param innermost True if all left-hand sides of dependency pairs are assumed to be instantiated
   *  with terms that are in normal form with respect to original.
   * @param flag All strict subterms of right-hand sides of DPs are expected to be instantiated to
   *  computable, terminating or arbitrary terms (with respect to original), as given by flag.
   */
  public Problem(List<DP> dps, List<Rule> rules, Set<Integer> privates, TRS original,
                 boolean innermost, boolean extraRules, TerminationFlag flag) {
    if (dps == null) throw new NullStorageException("Problem", "set of dependency pairs");
    if (rules == null) throw new NullStorageException("Problem", "set of rules");
    if (original == null) throw new NullStorageException("Problem", "original TRS");
    _dps = dps;
    _rules = rules;
    _privateIndexes = privates == null ? Set.of() : privates;
    _originalTrs = original;
    _innermost = innermost;
    _extraRules = extraRules;
    _terminationFlag = flag;
  }

  /** Returns true if the DP problem is solved: the set of DPs is empty. */
  public boolean isEmpty() {
    return _dps.isEmpty();
  }

  public List<DP> getDPList() {
    return _dps;
  }

  public List<Rule> getRuleList() {
    return _rules;
  }

  public boolean hasExtraRules() {
    return _extraRules;
  }

  public TRS getOriginalTRS() {
    return _originalTrs;
  }

  public boolean hasPrivateDPs() {
    return !_privateIndexes.isEmpty();
  }

  public boolean isPrivate(int dpIndex) {
    return _privateIndexes.contains(dpIndex);
  }

  public boolean isInnermost() {
    return _innermost;
  }

  public TerminationFlag queryTerminationStatus() {
    return _terminationFlag;
  }

  /** Returns whether the termination flag implies termination */
  public boolean terminating() {
    return switch(_terminationFlag) {
      case Arbitrary -> false;
      case Terminating -> true;
      case Computable -> true;
    };
  }

  /** Returns a set with all the head symbols of dependency pairs */
  public Set<FunctionSymbol> getHeads() {
    Set<FunctionSymbol> allFns = new TreeSet<>();
    for (DP dp : _dps) {
      if (dp.lhs().isFunctionalTerm()) allFns.add(dp.lhs().queryRoot());
      if (dp.rhs().isFunctionalTerm()) allFns.add(dp.lhs().queryRoot());
    }
    return allFns;
  }

  /**
   * This function creates a copy of the current Problem with the given dependency pairs removed.
   * In addition, if emptyPrivates is set to true, then the new Problem will have an empty set of
   * private dependency pairs; if it is set to false, then a remaining DP is private in the new
   * problem if and only if it is private in the old problem.
   */
  public Problem removeDPs(Set<Integer> remove, boolean emptyPrivates) {
    List<DP> newList = new ArrayList<DP>();
    Set<Integer> newPriv = new TreeSet<Integer>();
    for (int i = 0; i < _dps.size(); i++) {
      if (remove.contains(i)) continue;
      if (!emptyPrivates && _privateIndexes.contains(i)) newPriv.add(newList.size());
      newList.add(_dps.get(i));
    }
    return new Problem(newList, _rules, newPriv, _originalTrs, _innermost, _extraRules,
                       _terminationFlag);
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    builder.append("DPs:\n");
    for (int i = 0; i < _dps.size(); i++) {
      builder.append("  ");
      builder.append(_dps.get(i).toString());
      if (_privateIndexes.contains(i)) builder.append(" (private)\n");
      else builder.append("\n");
    }
    builder.append("Rules:\n");
    for (int i = 0; i < _rules.size(); i++) {
      builder.append("  ");
      builder.append(_rules.get(i).toString());
      builder.append("\n");
    }
    if (_extraRules) builder.append("  ... and an unknown number of additional rules\n");
    builder.append("Evaluation is " + (_innermost ? "innermost" : "arbitrary") + ".\n");
    builder.append("Right-hand sides are expected to be " + _terminationFlag + ".\n");
    return builder.toString();
  }
}
