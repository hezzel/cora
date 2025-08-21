/**************************************************************************************************
 Copyright 2025 Cynthia Kop

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
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;

/**
 * Several deduction rules introduce fresh variables.  This class is used to come up with suitable
 * names for these variables, taking into account their origin and the naming of variables in the
 * TRS rules.
 */
public class VariableNamer {
  private TreeMap<String,String> _defaultNames;
  public record VariableInfo(String basename, int index) {}

  /**
   * Created by ProofContext, the constructor takes as argument all occurrences of (f,i,xname) such
   * that a rule left-hand side f(s1,...,si,...,sn) occurs where si is a variable named xname.
   * This is used to store, in _defaultNames, a pair f:i ⇒ xname if the element at position i below
   * f *always* has this name in the left-hand side of a rule.
   */
  VariableNamer(ArrayList<Pair<Pair<FunctionSymbol,Integer>,String>> info) {
    TreeMap<String,TreeSet<String>> usualNames = new TreeMap<String,TreeSet<String>>();
    for (Pair<Pair<FunctionSymbol,Integer>,String> pair : info) {
      FunctionSymbol f = pair.fst().fst();
      int index = pair.fst().snd();
      String name = pair.snd();
      int n = name.length();
      while (n > 0 && Character.isDigit(name.charAt(n-1))) n--;
      if (n == 0) continue;
      name = name.substring(0, n);
      String key = f.queryName() + ":" + index;
      if (!usualNames.containsKey(key)) usualNames.put(key, new TreeSet<String>());
      usualNames.get(key).add(name);
    }
    _defaultNames = new TreeMap<String,String>();
    for (Map.Entry<String,TreeSet<String>> entry : usualNames.entrySet()) {
      if (entry.getValue().size() == 1) {
        _defaultNames.put(entry.getKey(), entry.getValue().first());
      }
    }
  }

  /**
   * In some cases, the immediate argument of a function symbol always has the same base name in
   * the left-hand sides of rules.  In that case, when creating a new variable at this position, it
   * may be a good idea to use the same name!  If the given function symbol / index combination has
   * such a default name, this function returns it; otherwise, null is returned.
   */
  public String queryDefaultNaming(FunctionSymbol f, int index) {
    return _defaultNames.get(f.queryName() + ":" + index);
  }

  /**
   * Given a user-suggested variable name [fullName], this splits it up into an appropriate base
   * name and index.
   */
  public VariableInfo getVariableInfo(String fullName) {
    int index = fullName.length();
    while (index > 0 && Character.isDigit(fullName.charAt(index-1))) index--;
    if (index == fullName.length()) return new VariableInfo(fullName, 0);
    int num = Integer.parseInt(fullName.substring(index));
    if (index == 0) return new VariableInfo("var", num);
    return new VariableInfo(fullName.substring(0, index), num);
  }

  /**
   * Given a variable with name [baseName], that is called [fullName] in a renaming, this
   * interprets the variable as a combination of name and index.  This might just be
   * ([fullName],0), but especially if the variable was created by the VariableNamer, there could
   * be a clearer division.
   */
  public VariableInfo getVariableInfo(String baseName, String fullName) {
    if (fullName == null) fullName = baseName;
    VariableInfo ret = getVariableInfo(fullName);
    if (baseName.length() < ret.basename().length() &&
        ret.basename().substring(0, baseName.length()).equals(baseName)) {
      return new VariableInfo(baseName, ret.index());
    }
    return ret;
  }

  /**
   * For creating a new variable that is derived from x (for example, it's one of the variables
   * needed in a case analysis on x), this function returns an appropriate base name and index,
   * so that <basename><index> is available to be used in the given renaming.
   *
   * The renaming is not modified, but should be modifiable so that availability can be checked.
   */
  public VariableInfo chooseDerivativeNaming(Variable x, MutableRenaming renaming) {
    String basename = x.queryName();
    String fullname = renaming.getName(x);
    if (fullname == null) fullname = basename;
    VariableInfo current = getVariableInfo(basename, fullname);
    for (int i = current.index + 1; ; i++) {
      String suggestedName = current.basename() + i;
      if (renaming.isAvailable(suggestedName)) return new VariableInfo(current.basename(), i);
    }
  }

  /** 
   * For creating a new variable that is derived from t, this function returns an appropriate base
   * name and index, so that <basename><index> does not occur in the given renaming.  For the base
   * name, we either choose a variable from t if there is only one, or we choose the given default
   * base; for the index we check which variables from that default occur inside t.
   *
   * The renaming is not modified, but should be modifiable so that availability can be checked.
   */  
  public VariableInfo chooseDerivativeNamingForTerm(Term t, MutableRenaming renaming,
                                                    String defaultName) {
    TreeSet<Variable> set = getSuitableVariablesForDerivative(t);
    String base = null;
    // if all variables in t have the same base name, that's our base
    if (set.size() > 0) {
      boolean first = true;
      for (Variable y : set) {
        VariableInfo info = getVariableInfo(y.queryName(), renaming.getName(y));
        if (first) { first = false; base = info.basename(); }
        else if (!base.equals(info.basename())) { base = null; break; }
      }
    }
    // otherwise, we use the defaultName as the base
    if (base == null) base = defaultName;
    // let's pick an index beyond what's already in t
    int index = 1;
    for (Variable x : set) {
      String fullname = renaming.getName(x);
      if (fullname == null) fullname = x.queryName();
      VariableInfo info = getVariableInfo(base, fullname);
      if (info.basename().equals(base) && info.index() >= index) index = info.index() + 1;
    }
    while (!renaming.isAvailable(base + index)) index++;
    return new VariableInfo(base, index);
  }

  /**
   * This helper function returns the variables in the given term that have the same type as the
   * given term, and which therefore are likely candidates to take a derivative name from.
   */
  public TreeSet<Variable> getSuitableVariablesForDerivative(Term term) {
    TreeSet<Variable> set = new TreeSet<Variable>();
    for (Variable x : term.vars()) {
      if (x.queryType().equals(term.queryType())) set.add(x);
    }
    return set;
  }

  /**
   * This function creates a new variable of the given type, whose name is chosen as a derivative
   * of x (for example, if x is named var203, then the new variable will be named var204).
   * The new variable will be immediately stored in the renaming.
   */
  public Variable chooseDerivative(Variable x, MutableRenaming renaming, Type type) {
    VariableInfo info = chooseDerivativeNaming(x, renaming);
    Variable newvar = TermFactory.createVar(info.basename(), type);
    renaming.setName(newvar, info.basename() + info.index());
    return newvar;
  }

  /**
   * This function creates a new variable of the given type, whose name is chosen as either the
   * same as x, if that is available, or otherwise as a derivative of x (as in chooseDerivative).
   * The new variable will be immediately stored in the renaming.
   */
  public Variable chooseDerivativeOrSameNaming(Variable x, MutableRenaming renaming, Type type) {
    VariableInfo info = chooseDerivativeNaming(x, renaming);
    Variable newvar = TermFactory.createVar(info.basename(), type);
    if (renaming.getName(x) == null && renaming.getReplaceable(x.queryName()) == null) {
      if (renaming.setName(newvar, x.queryName())) return newvar;
    }
    renaming.setName(newvar, info.basename() + info.index());
    return newvar;
  }

  /**
   * This function finds a suitable name for a new variable of the same type as t, which is in some
   * way based on t.  Specifically, it does so as follows:
   * - if t contains exactly one variable, the new variable will be a derivative of it
   * - otherwise, if occursInside is a pair (f,i) such that all rules rooted by f have a form f ...
   *   x_i ... → r | φ where the name of x_i is always the same, then this name will be used as the
   *   basis for the naming
   * - otherwise, we use defbase as the base name for the new variable
   * Note that occursInside is allowed to be null, in which case the second option does not happen.
   *
   * The new variable will be immediately stored in the renaming.
   */
  public Variable chooseDerivativeForTerm(Term t, MutableRenaming renaming, String defbase,
                                          Pair<FunctionSymbol,Integer> occursInside) {
    if (occursInside != null) {
      String placename = queryDefaultNaming(occursInside.fst(), occursInside.snd());
      if (placename != null) defbase = placename;
    }
    VariableInfo info = chooseDerivativeNamingForTerm(t, renaming, defbase);
    Variable x = TermFactory.createVar(info.basename(), t.queryType());
    if (!renaming.setName(x, info.basename() + info.index())) throw new RuntimeException(
      "Unexpected behaviour in chooseDerivativeForTerm, name = " + info.basename() + info.index());
    return x;
  }
}

