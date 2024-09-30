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

import charlie.types.*;
import charlie.terms.*;
import charlie.trs.*;

import java.util.ArrayList;
import java.util.Optional;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * This class generates the DP problem for a given TRS, under different settings (e.g., full or
 * call-by-value strategy; termination or universal computability).
 */
public class DPGenerator {
  private TRS _trs;
  private Base _dpSort;
  private TreeMap<FunctionSymbol,FunctionSymbol> _sharpSymbols;
  private TreeMap<FunctionSymbol,FunctionSymbol> _originalSymbols;
  private TreeSet<String> _usedNames;
  private ArrayList<DP> _dps;
  private Alphabet _extendedAlphabet;

  /**
   * On construction, the DP generator immediately computes the dependency pairs of the given TRS.
   * The result can then be converted to a DP Problem using queryProblem().  The other query
   * functions provide additional information on the generated problem.
   */
  public DPGenerator(TRS trs) {
    _trs = trs;
    _dpSort = chooseDPSort();
    _sharpSymbols = new TreeMap<FunctionSymbol,FunctionSymbol>();
    _originalSymbols = new TreeMap<FunctionSymbol,FunctionSymbol>();
    _usedNames = new TreeSet<String>();
    _dps = new ArrayList<DP>();
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      storeDPsForRule(_trs.queryRule(i));
    }
    _extendedAlphabet = _trs.queryAlphabet().add(_sharpSymbols.values());
  }

  /** Returns the output sort that is used for all DPs. */
  public Base queryDPSort() {
    return _dpSort;
  }

  /**
   * Returns the sharp function symbol for the given symbol, if any, or empty if none has been
   * generated (for example because the function symbol is not a defined symbol).
   */
  public Optional<FunctionSymbol> querySharpSymbolFor(FunctionSymbol f) {
    FunctionSymbol ret = _sharpSymbols.get(f);
    if (ret == null) return Optional.empty();
    else return Optional.of(ret);
  }

  /**
   * Returns the symbol f for a given sharp symbol f#.  If the given function symbol is not a
   * sharp symbol that we know about, it returns empty instead.
   */
  public Optional<FunctionSymbol> queryUnsharpSymbolFor(FunctionSymbol f) {
    FunctionSymbol ret = _originalSymbols.get(f);
    if (ret == null) return Optional.empty();
    else return Optional.of(ret);
  }

  /**
   * This returns the initial DP problem for the given settings.
   * Note that the "original" TRS in the problem is the TRS that we were generated with, but with
   * its alphabet extended to include the sharped symbols.
   */
  public Problem queryProblem(boolean innermost, boolean extraRules) {
    TreeSet<Integer> priv = new TreeSet<Integer>();
    for (int i = 0; i < _dps.size(); i++) {
      if (_trs.isPrivate(_originalSymbols.get(_dps.get(i).lhs().queryRoot()))) priv.add(i);
    }
    TRS newtrs = _trs.createDerivative(_trs.queryRules(), _extendedAlphabet);
    return new Problem(_dps, _trs.queryRules(), priv, newtrs, innermost, extraRules,
                       Problem.TerminationFlag.Computable);
  }

  /**
   * Helper function for the constructor (so may only use _trs of the global variables): chooses
   * the sort to use as the output sort for the sharped function symbols.
   */
  private Base chooseDPSort() {
    // collect all the sorts used in the alphabet of _trs
    TreeSet<String> sorts = new TreeSet<String>();
    ArrayList<Type> types = new ArrayList<Type>();
    for (FunctionSymbol f : _trs.queryAlphabet().getSymbols()) types.add(f.queryType());
    for (int i = 0; i < types.size(); i++) {
      if (types.get(i) instanceof Base(String name)) sorts.add(name);
      for (int j = 1; j <= types.get(i).numberSubtypes(); j++) types.add(types.get(i).subtype(j));
    }

    // choose an unused one!
    if (!sorts.contains("dpsort")) return TypeFactory.createSort("dpsort");
    if (!sorts.contains("DPSORT")) return TypeFactory.createSort("DPSORT");
    if (!sorts.contains("dp_sort")) return TypeFactory.createSort("dp_sort");
    if (!sorts.contains("DP_SORT")) return TypeFactory.createSort("DP_SORT");
    for (int i = 1; ; i++) {
      String attempt = "dpsort" + i;
      if (!sorts.contains(attempt)) return TypeFactory.createSort(attempt);
    }
  }

  /**
   * Given a type A1 → ... → An → B with b a sort or product type, this method returns the type
   * A1 → ... → An → dpSort, where dpSort is the special (otherwise unused) sort we use as the
   * output type of all dependency pairs.
   */
  private Type generateDpType(Type ty) {
    return switch(ty) {
      case Base(_), Product(_) -> _dpSort;
      case Arrow(Type left, Type right) -> TypeFactory.createArrow(left, generateDpType(right));
    };
  }

  /**
   * Given a function symbol f : A1 ⇒ ... ⇒ An ⇒ ι, this method generates a new function symbol
   * f# : A1 ⇒ ... ⇒ An ⇒ dp_sort.
   */
  private FunctionSymbol generateSharpFn(FunctionSymbol fn) {
    if (_sharpSymbols.containsKey(fn)) return _sharpSymbols.get(fn);
    String newname = fn.queryName() + "#";
    for (int i = 1; _trs.lookupSymbol(newname) != null || _usedNames.contains(newname); i++) {
      newname = fn.queryName() + "#" + i + "";
    }
    FunctionSymbol ret = TermFactory.createConstant(newname, generateDpType(fn.queryType()));
    _sharpSymbols.put(fn, ret);
    _originalSymbols.put(ret, fn);
    _usedNames.add(newname);
    return ret;
  }

  /**
   * Given a term f(s1,...,sn), this returns the term f#(s1,...,sn).  If necessary, the function
   * symbol f# is generated and stored in _sharpSymbols first.
   * If the given term is not a functional term, this yields an InappropriatePatternDataException.
   */
  private Term generateSharpTm(Term tm) {
    FunctionSymbol newHead = generateSharpFn(tm.queryRoot());
    return newHead.apply(tm.queryArguments());
  }

  /**
   * Given a type A1 ⇒ ... ⇒ An ⇒ ι, this returns a list of variables X1, ..., Xn such that
   * each variable Xi is of type Ai.  If the given type is not an arrow type, then the returned
   * list is empty.
   * The default names for the given variables are basename + startIndex, basename +
   * (startIndex + 1), ...
   */
  private ArrayList<Term> generateFlatteningVars(Type ty, String basename, int startIndex) {
    ArrayList<Term> ret = new ArrayList<Term>();
    while (ty instanceof Arrow(Type left, Type right)) {
      ret.add(TermFactory.createVar(basename + startIndex, left));
      startIndex++;
      ty = right;
    }
    return ret;
  }

  /**
   * Given a term term r, this returns the list of all subterms of r whose root symbol is a defined
   * symbol in _trs, flattened to base type with fresh variables.  These are the candidates that
   * will be used to generate dependency pairs from.
   */
  private ArrayList<Term> generateCandidates(Term tm) {
    ArrayList<Term> cands = new ArrayList<Term>();
    tm.visitSubterms( (s,p) -> {
      if (s.isFunctionalTerm()) {
        FunctionSymbol f = s.queryRoot();
        if (_trs.isDefined(f)) {
          cands.add(s.apply(generateFlatteningVars(s.queryType(), "fresh", 1)));
        }
      }
    } );
    return cands;
  }

  /** This function computes the dependency pairs for the given rule, and stores them into _dps. */
  private void storeDPsForRule(Rule rule) {
    Term lhs = rule.queryLeftSide();
    Term rhs = rule.queryRightSide();
    Term ctr = rule.queryConstraint();

    // flatten left- and right-hand side to base type by adding extra variables
    ArrayList<Term> xs = generateFlatteningVars(lhs.queryType(), "arg", lhs.numberArguments()+1);
    lhs = lhs.apply(xs);
    rhs = rhs.apply(xs);

    Term dpLeft = generateSharpTm(lhs);
    ArrayList<Term> cands = generateCandidates(rhs);
    for (Term candidate : cands) {
      _dps.add(new DP(dpLeft, generateSharpTm(candidate), ctr));
    }
  }
}

