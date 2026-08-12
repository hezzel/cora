/**************************************************************************************************
 Copyright 2019--2026 Cynthia Kop

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

import java.util.ArrayList;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TVarSet;
import charlie.terms.position.Position;
import charlie.terms.position.FinalPos;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.ReplaceableSet;

/**
 * A TermInherit supplies default functionality for all instances of Term.
 * 
 * This is the functionality that calls other functions in Term to for instance build up an
 * environment.  It also includes some functionality that is meant to be overwritten in only
 * specific kinds of subterms, e.g., providing a default value false for the function
 * isConstant().
 *
 * All inheriting classes should make sure to call setVariables in their constructor, to set up
 * the set of variables (both free and bound!), meta-variables and type variables occurring in the
 * term.  Moreover, they should make sure that the term is well-behaved; that is, that the same
 * variable does not occur both free and bound in the term.  The function
 * calculateBoundVariablesAndRefreshSubs can be used for this purpose.
 */
abstract class TermInherit implements Term {
  private TVarSet _typeVariables;
  private ReplaceableSet _freeReplaceables;
  private ReplaceableSet _boundVariables;

  /**
   * Sets the set of all meta-variables and free variables occurring in this term to vs, the
   * set of bound variables to empty, and the set of type variables to ts.
   * One of the setVariables functions should be called from the constructor, and only there.
   */
  protected final void setVariables(ReplaceableSet vs, TVarSet ts) {
    if (_freeReplaceables != null) throw new RuntimeException("Setting ReplaceableSet twice for " +
      this.getClass().getSimpleName());
    _typeVariables = ts;
    _freeReplaceables = vs;
    _boundVariables = ReplaceableSet.EMPTY;
  }

  /**
   * Sets the sets of all free/meta and all bound variables, as well as all type variables,
   * occuring in this term.  Bounds is allowed to be null, in which case the empty set is used.
   * One of the setVariables functions should be called from the constructor, and only there.
   */
  protected final void setVariables(ReplaceableSet frees, ReplaceableSet bounds, TVarSet types) {
    if (_freeReplaceables != null) throw new RuntimeException("Setting ReplaceableSet twice for " +
      this.getClass().getSimpleName());
    _freeReplaceables = frees;
    if (bounds == null) _boundVariables = ReplaceableSet.EMPTY;
    else _boundVariables = bounds;
    _typeVariables = types;
  }

  /** Returns a combined type variable set for the given subterms, which also includes extra. */
  protected static TVarSet calculateTypeVariablesForSubterms(List<Term> subs, TVarSet extra) {
    TVarSet result = extra;
    for (int i = 0; i < subs.size(); i++) {
      result = result.combine(subs.get(i).queryTypeVars());
    }
    return result;
  }

  /** Returns a combined replaceable set for the given subterms, which also includes extra. */
  protected static ReplaceableSet calculateFreeReplaceablesForSubterms(List<Term> subs,
                                                                       ReplaceableSet extra) {
    ReplaceableSet largest = extra;
    int best = 0;
    for (int i = 0; i < subs.size(); i++) {
      if (subs.get(i).freeReplaceables().size() > largest.size()) {
        best = i + 1;
        largest = subs.get(i).freeReplaceables();
      }
    }
    // combine the rest into it!
    ReplaceableSet frees = largest;
    if (best != 0) frees = frees.combine(extra);
    for (int i = 0; i < subs.size(); i++) {
      if (best != i + 1) frees = frees.combine(subs.get(i).freeReplaceables());
    }
    return frees;
  }

  /**
   * Refreshes bound variables in the given list if necessary to ensure that they do not overlap
   * with the variables in the given "avoid" set (to ensure well-behavedness of terms), and stores
   * the resulting terms (or original terms if they already do not overlap) in the given list
   * updatedSubs.
   * Note that subs itself is not changed.  The function returns the resulting combined set of
   * bound variables, including all those in "include".
   */
  protected static ReplaceableSet calculateBoundVariablesAndRefreshSubs(List<Term> subs,
                                        ReplaceableSet include, ReplaceableSet avoid,
                                        List<Term> updatedSubs) {
    for (int i = 0; i < subs.size(); i++) {
      Term sub = subs.get(i);
      ReplaceableSet vs = sub.boundVars();
      if (vs.size() > 0) {
        if (!vs.getOverlap(avoid).isEmpty()) {
          sub = sub.renameAndRefreshBinders(new TreeMap<Variable,Variable>());
          vs = sub.boundVars();
        }
        if (include.size() == 0) include = vs;
        else include = include.combine(vs);
      }
      updatedSubs.add(sub);
    }
    return include;
  }

  /** Returns the set of all variables occurring free in the current term. */
  public final Environment<Variable> vars() {
    if (_freeReplaceables == null) throw new RuntimeException("Variable list requested when it " +
      "has not been set up for " + this.getClass().getSimpleName());
    return new VariableEnvironment(_freeReplaceables);
  }

  /** Returns the set of all meta-variables occurring in the current term. */
  public final Environment<MetaVariable> mvars() {
    if (_freeReplaceables == null) throw new RuntimeException("Meta-variable list requested when " +
      "it has not been set up for " + this.getClass().getSimpleName());
    return new MetaVariableEnvironment(_freeReplaceables);
  }

  /** Returns the set of all meta-variables and variables occurring free in the current term. */
  public final ReplaceableSet freeReplaceables() {
    if (_freeReplaceables == null) throw new RuntimeException("Replaceable set has not been set " +
      "up for " + this.getClass().getSimpleName() + " when requesting free replaceables.");
    return _freeReplaceables;
  }

  /** Returns the set of all variables occurring bound in the current term. */
  public final ReplaceableSet boundVars() {
    if (_freeReplaceables == null) throw new RuntimeException("Replaceable set has not been set " +
      "up for " + this.getClass().getSimpleName() + " when requesting bound variables");
    return _boundVariables;
  }

  /** Returns the set of all type variables that occur in the current term. */
  public final TVarSet queryTypeVars() {
    if (_typeVariables == null) throw new RuntimeException("Type variable set has not been " +
      "set up for " + this.getClass().getSimpleName());
    return _typeVariables;
  }

  /** Returns true if there are no free variables or meta-variables. */
  public final boolean isGround() {
    return _freeReplaceables.size() == 0;
  }

  /** Returns true if freeReplaceables() contains no binder variables. */
  public final boolean isClosed() {
    ReplaceableSet vs = freeReplaceables();
    for (Replaceable x : vs) {
      if (x.queryReplaceableKind() == Replaceable.Kind.BINDER) return false;
    }
    return true;
  }

  /**
   * Returns true if every meta-variable occurring freely occurs only once
   * (where non-binder variables are also counted as meta-variables, but binders are not!)
   */
  public final boolean isLinear() {
    TreeSet<MetaVariable> mvars = new TreeSet<MetaVariable>();
    for (Pair<Term,Position> p : querySubterms()) {
      if (p.fst().isMetaApplication()) {
        MetaVariable x = p.fst().queryMetaVariable();
        if (mvars.contains(x)) return false;
        mvars.add(x);
      }
    }
    return true;
  }

  /** Returns true if freeReplaceables() contains no meta-variables other than variables. */
  public final boolean isTrueTerm() {
    ReplaceableSet vs = freeReplaceables();
    for (Replaceable x : vs) {
      if (x.queryReplaceableKind() == Replaceable.Kind.METAVAR) return false;
    }
    return true;
  }

  /** Returns true if no type variables occur in the present term. */
  public final boolean isMonomorphic() {
    return _typeVariables.isEmpty();
  }

  /** Helper function to return the current classname for use in Exceptions. */
  protected final String queryMyClassName() {
    return this.getClass().getSimpleName();
  }

  /**
   * Returns the set of all positions for this term (including partial positions if and only if
   * the "partial" argument is true).
   */
  public final ArrayList<Position> queryPositions(boolean partial) {
    List<Pair<Term,Position>> subs = querySubterms();
    ArrayList<Position> ret = new ArrayList<Position>();
    for (Pair<Term,Position> pair : subs) {
      Position p = pair.snd();
      if (partial) {
        for (int j = pair.fst().numberArguments(); j > 0; j--) ret.add(p.append(new FinalPos(j)));
      }
      ret.add(p);
    }
    return ret;
  }

  /** Returns whether all alpha-equal variants of this have other as a subterm. */
  public final boolean hasSubterm(Term other) {
    for (Pair<Term,Position> p : querySubterms()) {
      if (p.fst().equals(other)) {
        // check that other doesn't freely contain binder variables that are bound in us
        for (Replaceable x : other.freeReplaceables()) {
          if (x.queryReplaceableKind() == Replaceable.Kind.BINDER &&
              !_freeReplaceables.contains(x)) return false;
        }
        return true;
      }
    }
    return false;
  }

  /** This function should handle querySubterm(pos), but may skip the case for an empty position. */
  protected abstract Term querySubtermMain(Position pos);

  /**
   * This function returns the subterm at position pos if pos is an empty position, and if not,
   * delegates the work to queryNonEmptySubterm(pos).
   */
  public final Term querySubterm(Position pos) {
    switch (pos) {
      case FinalPos(int k):
        if (k == 0) return this;
        // deliberately skipping to default for final non-empty positions
      default:
        return querySubtermMain(pos);
    }
  }

  /**
   * This function should handle replaceSubterm(pos, replacement), but may skip the case for an
   * empty position.
   */
  protected abstract Term replaceSubtermMain(Position pos, Term replacement);

  public final Term replaceSubterm(Position pos, Term replacement) {
    switch (pos) {
      case FinalPos(int k):
        if (k == 0) {
          if (!queryType().equals(replacement.queryType())) {
            throw new TypingException("Typing error: cannot replace ", this, " (of type ",
              queryType(), ") by ", replacement, " (of type ", replacement.queryType(), ").");
          }
          return replacement;
        }
        // deliberately skipping to default for final non-empty positions
      default:
        return replaceSubtermMain(pos, replacement);
    }
  }

  /** Executes the given function on all subterms. */
  public final void visitSubterms(BiConsumer<Term,Position> vis) {
    for (Pair<Term,Position> p : querySubterms()) {
      vis.accept(p.fst(), p.snd());
    }
  }

  /** Returns the first subterm/position pair where vis returns true (if any) */
  public final Pair<Term,Position> findSubterm(BiFunction<Term,Position,Boolean> vis) {
    for (Pair<Term,Position> p : querySubterms()) {
      if (vis.apply(p.fst(), p.snd())) return p;
    }
    return null;
  }

  /** Applies the current term (with functional type) to other. */
  public final Term apply(Term other) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(other);
    return apply(args);
  }

  /** 
   * If the current term is h(t1,...,tk) and has a type σ1 →...→ σn → τ and args = [s1,...,sn] with
   * each si : σi, then this function returns h(t1,...,tk,s1,...,sn).
   */
  public final Term apply(List<Term> args) {
    if (args.size() == 0) return this;
    return new Application(this, args);
  }

  /** Applies the given substitution to the present term. */
  public final Term substitute(ISubstitution subst) {
    return subst.applySubstitution(this);
  }

  /** This method verifies equality to another Term. */
  public final boolean equals(Term other) {
    if (other == null) return false;
    TreeMap<Variable,Integer> mu = new TreeMap<Variable,Integer>();
    TreeMap<Variable,Integer> xi = new TreeMap<Variable,Integer>();
    return alphaEquals(other, mu, xi, 1);
  }

  /** This method verifies equality to another Java object. */
  public final boolean equals(Object other) {
    if (other instanceof Term) return equals((Term)other);
    return false;
  }

  /** This method returns a hashcode consistent with equality */
  @Override
  public final int hashCode() {
    return hashCode(null);
  }

  /** This method returns a string representation of the current term. */
  public final String toString() {
    return TermPrinter.DEBUGPRINTER.print(this);
  }

  // the following functions are all default implementations of interface functions, to be
  // overwritten only in one or two of the inheriting classes

  public boolean isVariable() { return false; }
  public boolean isConstant() { return false; }
  public boolean isFunctionalTerm() { return false; }
  public boolean isVarTerm() { return false; }
  public boolean isApplication() { return false; }
  public boolean isAbstraction() { return false; }
  public boolean isMetaApplication() { return false; }
  public boolean isTuple() { return false; }
  public boolean isBetaRedex() { return false; }
  public boolean isValue() { return false; }
  public Value toValue() { return null; }
  public int numberArguments() { return 0; }
  public int numberMetaArguments() { return 0; }
  public int numberTupleArguments() { return 0; }
  public ArrayList<Term> queryArguments() { return new ArrayList<Term>(); }
  public ArrayList<Term> queryTupleArguments() { return new ArrayList<Term>(); }
  public ArrayList<Term> queryMetaArguments() { return new ArrayList<Term>(); }
  public Term queryHead() { return this; }
  public Term queryArgument(int i) {
    throw new IndexOutOfBoundsException(queryMyClassName() + "::queryArgument(" + i + ") called.");
  }
  public Term queryMetaArgument(int i) {
    throw new IndexOutOfBoundsException(queryMyClassName() + "::queryMetaArgument(" + i +
      ") called.");
  }
  public Term queryTupleArgument(int i) {
    throw new IndexOutOfBoundsException(queryMyClassName() + "::queryTupleArgument(" + i +
      ") called.");
  }
  public Term queryImmediateHeadSubterm(int i) {
    if (i == 0) return this;
    throw new IndexOutOfBoundsException(queryMyClassName() + "::queryImmediateHeadSubterm(" + i +
      ") called.");
  }
  public Term queryAbstractionSubterm() {
    throw new InappropriatePatternDataException(queryMyClassName(), "queryAbstractionSubterm",
      "abstractions");
  }
  public FunctionSymbol queryRoot() {
    throw new InappropriatePatternDataException(queryMyClassName(),"queryRoot","functional terms");
  }
}

