/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import cora.exceptions.*;
import cora.utils.Pair;
import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.position.Position;
import cora.terms.position.LambdaPos;

/** Abstractions are terms of the form λx.s where x is a variable and s a term. */
class Abstraction extends TermInherit {
  private Variable _binder;
  private Term _subterm;
  private Type _type;

  /**
   * Generates the abstraction λ<binder>.<subterm>.
   * Throws an IllegalArgumentError if the given binder is not marked as a binder variable.
   */
  public Abstraction(Variable binder, Term subterm) {
    if (binder == null) throw new NullInitialisationError("Abstraction", "binder");
    if (subterm == null) throw new NullInitialisationError("Abstraction", "subterm");
    if (!binder.isBinderVariable()) {
      throw new IllegalTermError("Abstraction", binder.toString() + " is not marked as a binder.");
    }
    // to guarantee well-behavedness, make sure that subterm does not already bind the binder
    if (subterm.boundVars().contains(binder)) subterm = subterm.refreshBinders();
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

  /** @return the subterm s for an abstraction λx.s */
  @Override
  public Term queryAbstractionSubterm() {
    return _subterm;
  }

  /** @throws InappropriatePatternDataError, as an abstraction is not a meta-application */
  public MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataError("Abstraction", "queryMetaVariable", "meta-variable " +
      "applications or terms with meta-variable applications as the head");
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
        throw new IndexingError("Abstraction", "querySubterm", toString(), pos.toString());
    }
  }

  /** @return the current term with the subterm at pos replaced by replacement (pos is non-empty) */
  public Term replaceSubtermMain(Position pos, Term replacement) {
    switch (pos) {
      case LambdaPos(Position tail):
        return new Abstraction(_binder, _subterm.replaceSubterm(pos.queryTail(), replacement));
      default:  
        throw new IndexingError("Abstraction", "replaceSubterm", toString(), pos.toString());
    }
  }

  /** (λx.s).substitute(γ) returns λz.(s.substitute(γ)), where z is fully fresh */
  public Term substitute(Substitution gamma) {
    Variable freshvar = new Binder(_binder.queryName(), _binder.queryType());
    Term subtermSubstitute;
    if (gamma.extend(_binder, freshvar)) {
      subtermSubstitute = _subterm.substitute(gamma);
      gamma.delete(_binder);
    }
    else {
      Term previous = gamma.get(_binder);
      gamma.replace(_binder, freshvar);
      subtermSubstitute = _subterm.substitute(gamma);
      gamma.replace(_binder, previous);
    }
    return new Abstraction(freshvar, subtermSubstitute);
  }

  /**
   * Updates γ so that this gamma =α other if possible, and returns a string describing the reason
   * for impossibility if not.
   * (λx.s)γ =α t   iff
   * λz.(s ([x:=z] ∪ (γ \ {x}))) =α t where z is fresh     iff
   * t = λy.t' and y ∉ FV( s ([x:=z] ∪ (γ \ {x})) ) \ {z} and (s ([x:=z] ∪ (γ \ {x}))) [z:=y] =α t'
   * iff (since z is fresh) all the following hold:
   * - t = λy.t'
   * - y ∉ FV( γ(a) ) for any a ∈ FV(s) \ {x}
   * - s ([x:=y] ∪ (γ \ {x})) =α t'
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("Var", "match", "other (matched term)");
    if (gamma == null) throw new NullCallError("Var", "match", "gamma (matching substitution");

    if (!other.isAbstraction()) {
      return "Abstraction " + toString() + " is not instantiated by " + other + ".";
    }

    Variable x = _binder;
    Variable y = other.queryVariable();

    Term backup = gamma.get(x);
    if (backup == null) gamma.extend(x, y);
    else gamma.replace(x, y);
    String ret = _subterm.match(other.queryAbstractionSubterm(), gamma);
    if (backup == null) gamma.delete(x);
    else gamma.replace(x, backup);

    if (ret != null) return ret;

    for (Replaceable z : freeReplaceables()) {
      Term gammaz = gamma.get(z);
      if (gammaz != null && gammaz.freeReplaceables().contains(y)) {
        return "Abstraction " + toString() + " is not instantiated by " + other.toString() +
          " because the induced mapping [" + z.toString() + " := " + gammaz.toString() +
          "] contains the binder variable of " + other.toString() + ".";
      }
    }

    return null;
  }

  /**
   * Appends a string representation of the current abstraction to the given string builder.
   * The binder is renamed if its default name occurs in avoid.
   */
  public void addToString(StringBuilder builder, Map<Replaceable,String> renaming, Set<String> avoid) {
    String bname = _binder.queryName();
    String name = bname;
    for (int i = 1; avoid.contains(name); i++) name = bname + i;
    renaming.put(_binder, name);
    avoid.add(name);

    builder.append("λ");
    builder.append(renaming.get(_binder));
    builder.append(".");
    _subterm.addToString(builder, renaming, avoid);

    avoid.remove(name);
    renaming.remove(_binder);
    // note that it is not possible that renaming[binder] was previously set, as this would violate
    // the well-definedness constraint; hence, we do not have to restore anything here
  }

  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isAbstraction()) return false;
    Variable x = _binder;
    Variable y = term.queryVariable();
    if (!x.queryType().equals(y.queryType())) return false;
    if (mu.containsKey(x)) {
      throw new IllegalTermError("Abstraction",
        "Calling alphaEquals when mu already maps " + x.toString() + ".");
    }   
    if (xi.containsKey(y)) {
      throw new IllegalTermError("Abstraction",
        "Calling alphaEquals when xi already maps " + y.toString() + ".");
    }   
    mu.put(x, k); 
    xi.put(y, k); 
    boolean retval = _subterm.alphaEquals(term.queryAbstractionSubterm(), mu, xi, k + 1); 
    mu.remove(x);
    xi.remove(y);
    return retval;
  }
}

