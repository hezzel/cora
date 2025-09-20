/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import charlie.util.NullStorageException;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.position.Position;
import charlie.terms.position.LambdaPos;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.ReplaceableList;

/** Abstractions are terms of the form λx.s where x is a variable and s a term. */
class Abstraction extends TermInherit {
  private Variable _binder;
  private Term _subterm;
  private Type _type;

  /**
   * Generates the abstraction λ<binder>.<subterm>.
   * Throws an IllegalArgumentException if the given binder is not marked as a binder variable.
   */
  public Abstraction(Variable binder, Term subterm) {
    if (binder == null) throw new NullStorageException("Abstraction", "binder");
    if (subterm == null) throw new NullStorageException("Abstraction", "subterm");
    if (!binder.isBinderVariable()) {
      throw new IllegalArgumentException("Trying to construct an abstraction whose binder " +
        binder.queryName() + " is not marked as a binder.");
    }
    // to guarantee well-behavedness, make sure that subterm does not already bind the binder
    if (subterm.boundVars().contains(binder)) {
      subterm = subterm.renameAndRefreshBinders(new TreeMap<Variable,Variable>());
    }
    _binder = binder;
    _subterm = subterm;
    _type = TypeFactory.createArrow(binder.queryType(), subterm.queryType());
    ReplaceableList frees = subterm.freeReplaceables().remove(binder);
    ReplaceableList bounds = subterm.boundVars().add(binder);
    setVariables(frees, bounds);
  }

  /** @return <type of binder> → <type of subterm> */
  @Override
  public Type queryType() {
    return _type;
  }

  /** @return true, since this is indeed an abstraction */
  @Override
  public boolean isAbstraction() {
    return true;
  }

  /**
   * @return whether the immediate subterm is a theory term, and the variable has a theory type.
   */
  @Override
  public boolean isTheoryTerm() {
    return _binder.queryType().isTheoryType() && _subterm.isTheoryTerm();
  }

  /** Adds all function symbols in the present term to storage. */
  @Override
  public void storeFunctionSymbols(Set<FunctionSymbol> storage) {
    _subterm.storeFunctionSymbols(storage);
  }

  /** @return the subterm s for an abstraction λx.s */
  @Override
  public Term queryAbstractionSubterm() {
    return _subterm;
  }

  /** @throws InappropriatePatternDataException, as an abstraction is not a meta-application */
  public MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataException("Abstraction", "queryMetaVariable",
      "meta-variable applications or terms with meta-variable applications as the head");
  }

  /** @return the binder of the abstraction */
  public Variable queryVariable() {
    return _binder;
  }

  /** @return false, since an abstraction is not first-ordre */
  public boolean isFirstOrder() {
    return false;
  }

  /** @return whether this abstraction is a pattern (if and only if the immediate subterm is) */
  public boolean isPattern() {
    return _subterm.isPattern();
  }

  /** @return whether this abstraction is a semi-pattern (iff the immediate subterm is) */
  public boolean isSemiPattern() {
    return _subterm.isSemiPattern();
  }

  /** @return false, as an applicative term cannot include abstractions. */
  public boolean isApplicative() {
    return false;
  }

  /**
   * @return the list of all (full) subterms in this term along with their positions, in
   * innermost-left order
   */
  public List<Pair<Term,Position>> querySubterms() {
    List<Pair<Term,Position>> ret = _subterm.querySubterms();
    for (int i = 0; i < ret.size(); i++) {
      ret.set(i, new Pair<Term,Position>(ret.get(i).fst(), new LambdaPos(ret.get(i).snd())));
    }
    ret.add(new Pair<Term,Position>(this, Position.empty));
    return ret;
  }

  /** @return the subterm at the given (non-empty) position */
  public Term querySubtermMain(Position pos) {
    switch (pos) {
      case LambdaPos(Position tail):
        return _subterm.querySubterm(tail);
      default:
        throw new InvalidPositionException(this, pos, "querying subterm of an abstraction");
    }
  }

  /** @return the current term with the subterm at pos replaced by replacement (pos is non-empty) */
  public Term replaceSubtermMain(Position pos, Term replacement) {
    switch (pos) {
      case LambdaPos(Position tail):
        return new Abstraction(_binder, _subterm.replaceSubterm(pos.queryTail(), replacement));
      default:  
        throw new InvalidPositionException(this, pos, "replacing subterm of an abstraction");
    }
  }

  public Term renameAndRefreshBinders(Map<Variable,Variable> renaming) {
    Variable freshvar = new Binder(_binder.queryName(), _binder.queryType());
    Variable previous = renaming.get(_binder);
    renaming.put(_binder, freshvar);
    Term subtermSubstitute = _subterm.renameAndRefreshBinders(renaming);
    if (previous == null) renaming.remove(_binder);
    else renaming.put(_binder, previous);
    return new Abstraction(freshvar, subtermSubstitute);
  }

  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isAbstraction()) return false;
    Variable x = _binder;
    Variable y = term.queryVariable();
    if (!x.queryType().equals(y.queryType())) return false;
    if (mu.containsKey(x)) {
      throw new IllegalArgumentException("Calling Abstraction::alphaEquals when mu already maps " +
        x.toString() + ".");
    }   
    if (xi.containsKey(y)) {
      throw new IllegalArgumentException("Calling Abstraction::alphaEquals when xi already maps " +
        y.toString() + ".");
    }   
    mu.put(x, k); 
    xi.put(y, k); 
    boolean retval = _subterm.alphaEquals(term.queryAbstractionSubterm(), mu, xi, k + 1); 
    mu.remove(x);
    xi.remove(y);
    return retval;
  }

  /** Returns a hashcode compatible with alpha-equivalence */
  public int hashCode(Map<Variable,Integer> mu) {
    if (mu == null) mu = new TreeMap<Variable,Integer>();
    mu.put(_binder, mu.size()+1);
    int ret = 3 * _subterm.hashCode(mu);
    mu.remove(_binder);
    return ret;
  }
}

