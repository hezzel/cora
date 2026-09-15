/**************************************************************************************************
 Copyright 2025--2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.substitution;

import java.util.ArrayList;
import java.util.Set;
import java.util.TreeSet;
import charlie.util.UserException;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.*;

/**
 * The matcher is a static class that is used to match a pattern against another term.
 */
public class Matcher {
  public static class MatchFailure extends UserException {
    private Set<Integer> _patterns, _instances;
    public MatchFailure(Set<Integer> pats, Set<Integer> insts, Object ...args) {
      super(args);
      _patterns = pats;
      _instances = insts;
    }
    public String toString() {
      return getMessage();
    }
    /**
     * This returns true if the given component (which should be between 0 and queryComponentCount()
     * - 1) originates from the pattern used for matching.
     */
    public boolean originatesFromPattern(int componentID) {
      return _patterns.contains(componentID);
    }
    /**
     * This returns true if the given component (which should be between 0 and queryComponentCount()
     * - 1) originates from the term originally given to the Matcher as instance.
     */
    public boolean originatesFromInstance(int componentID) {
      return _instances.contains(componentID);
    }
  }

  /**
   * This method returns the substitution gamma such that pattern gamma = instance, if such a
   * substitution exists; if it does not, then null is returned instead.
   * The substitution is fresh, and may be changed at the caller's leisure.
   */
  public static MutableSubstitution match(Term pattern, Term instance) {
    MutableSubstitution ret = new MutableSubstitution();
    if (extendMatch(pattern, instance, ret) == null) return ret;
    return null;
  }

  /**
   * This method extends subst so that pattern subst = instance, if that is possible.  In this case,
   * null is returned.
   * If it is not possible, then an appropriate MatchFailure is returned.
   */
  public static MatchFailure extendMatch(Term pattern, Term instance, MutableSubstitution subst) {
    if (pattern.isConstant()) {
      return extendMatchWithConstant(pattern.queryRoot(), instance, subst);
    }
    if (pattern.isVariable()) {
      return extendMatchWithVariable(pattern.queryVariable(), instance, subst);
    }
    else if (pattern.isMetaApplication()) {
      return extendMatchWithMeta(pattern, instance, subst);
    }
    else if (pattern.isApplication()) {
      return extendMatchWithApplication(pattern, instance, subst);
    }   
    else if (pattern.isAbstraction()) {
      return extendMatchWithAbstraction(pattern, instance, subst);
    }   
    else throw new IllegalArgumentException("Matcher::extendMatch called with a term that does " +
      "not have any of the standard term shapes!");
  }

  private static MatchFailure extendMatchWithConstant(FunctionSymbol symbol, Term instance,
                                                      MutableSubstitution gamma) {
    FunctionSymbol g = null;
    if (instance.isConstant()) {
      g = instance.queryRoot();
      if (symbol.match(g, gamma)) return null;
      else if (symbol.queryName().equals(g.queryName())) {
        return new MatchFailure(Set.of(1, 3), Set.of(5, 7),
          "Constant ", symbol, " (of type ", symbol.queryType(),
          ") is not instantiated by symbol ", g, " (of type ", g.queryType(), ").");
      }
    }
    // fall-through for both the case that instance is not a symbol, and it has a different name
    return new MatchFailure(Set.of(1), Set.of(3),
      "Constant ", symbol, " is not instantiated by ", instance, ".");
  }


  private static MatchFailure extendMatchWithVariable(Variable x, Term instance,
                                                      MutableSubstitution gamma) {
    Term previous = gamma.get(x);

    // if we have a previous mapping, x has to be mapped to the exact same thing now
    if (previous != null) {
      if (previous.equals(instance)) return null;
      return new MatchFailure(Set.of(1), Set.of(3, 5),
                              x.isBinderVariable() ? "Binder variable " : "Variable ",
                              x, " is mapped both to ", previous, " and to ", instance, ".");
    }

    // otherwise, we first see if the type matches, and then extend the variable
    if (x.queryType().match(instance.queryType(), gamma)) {
      gamma.extend(x, instance);
      return null;
    }

    // if not, we return an appropriate error message
    if (x.isMonomorphic()) {
      return new MatchFailure(Set.of(1), Set.of(3),
        "Variable ", x, " has a different type from ", instance, ".");
    }
    else {
      return new MatchFailure(Set.of(1, 3), Set.of(5, 7),
        "Type ", x.queryType(), " of variable ", x, " cannot be matched to type ",
          instance.queryType(), " of instance ", instance, ".");
    }
  }

  private static MatchFailure extendMatchWithMeta(Term metaApp, Term instance,
                                                  MutableSubstitution gamma) {
    // get all the substituted arguments, and make sure they are distinct bound variables
    ArrayList<Variable> substitutedArgs = checkMetaPattern(metaApp, gamma);
    // create abstraction
    Term ret = instance;
    for (int i = substitutedArgs.size()-1; i >= 0; i--) {
      ret = TermFactory.createAbstraction(substitutedArgs.get(i), ret);
    }   
    // if the meta-variable is already mapped in gamma, it must be to ret!
    MetaVariable metavar = metaApp.queryMetaVariable();
    Term previous = gamma.get(metavar);
    if (previous != null) {
      if (previous.equals(ret)) return null;
      return new MatchFailure(Set.of(1), Set.of(3, 5),
                              "Meta-variable ", metavar, " is mapped to both " , previous, 
                              " and to ", ret, ".");
    }
    // if the meta-variable is not yet mapped, check the type and add the mapping
    if (metaApp.queryType().match(instance.queryType(), gamma)) {
      gamma.extend(metavar, ret);
      return null;
    }
    else {
      return new MatchFailure(Set.of(1), Set.of(3),
                     "Cannot match ", metaApp, " against ", instance, " as types do not match.");
    }   
  }

  /**
   * Given a meta-variable application Z⟨s1,...,sn⟩, this function checks if (s1,...,sn) are
   * distinct binder variables, all of which are mapped to distinct variables by gamma.
   * If so, the list [γ(s1),...,γ(sn)] is returned.
   * If not, a PatternRequiredException is thrown instead.
   */
  private static ArrayList<Variable> checkMetaPattern(Term metaApp, Substitution gamma) {
    ArrayList<Variable> ret = new ArrayList<Variable>();
    TreeSet<Variable> sofar = new TreeSet<Variable>();
    for (int i = 1; i <= metaApp.queryNumberMetaArguments(); i++) {
      if (!metaApp.queryMetaArgument(i).isVariable()) throw new PatternRequiredException(metaApp,
        "matching", i+1, "is not a variable (let alone a bound variable)");
      Variable x = metaApp.queryMetaArgument(i).queryVariable();
      if (!x.isBinderVariable()) throw new PatternRequiredException(metaApp, "matching", i+1,
        "is not a binder variable.");
      Term replacement = gamma.get(x);
      if (replacement == null) throw new PatternRequiredException(metaApp, "matching", i+1,
        "is not bound in the context above this subterm.");
      if (!replacement.isVariable()) throw new PatternRequiredException(metaApp, "matching", i+1,
        "is substituted to a non-variable term in the context.");
      Variable y = replacement.queryVariable();
      if (!y.isBinderVariable()) throw new PatternRequiredException(metaApp, "matching", i+1,
        "is substituted to a non-binder variable in the context.");
      ret.add(y);
      if (sofar.contains(y)) throw new PatternRequiredException(metaApp, "matching", i+1,
        "is substituted to the same binder variable as a previous argument.");
      sofar.add(y);
    }
    return ret;
  }

  private static MatchFailure extendMatchWithApplication(Term pattern, Term instance,
                                                         MutableSubstitution gamma) {
    if (!instance.isApplication()) {
      return new MatchFailure(Set.of(3), Set.of(1),
        "The term ", instance, " does not instantiate ", pattern, " as it is not an application.");
    }
    if (instance.queryNumberArguments() < pattern.queryNumberArguments()) {
      return new MatchFailure(Set.of(3), Set.of(1), "The term ", instance,
        " does not instantiate ", pattern, " as it has too few arguments.");
    }
    int i = instance.queryNumberArguments();
    int j = pattern.queryNumberArguments();
    for (; j > 0; i--, j--) {
      Term patsub = pattern.queryArgument(j);
      Term inssub = instance.queryArgument(i);
      MatchFailure warning = extendMatch(patsub, inssub, gamma);
      if (warning != null) return warning;
    }
    return extendMatch(pattern.queryHead(), instance.queryImmediateHeadSubterm(i), gamma);
  }

  /**
   * Updates γ so that abs gamma =α instance if possible, and returns a MatchFailure describing
   * the reason for impossibility if not.  Note that:
   * (λx.s)γ =α t   iff
   * λz.(s ([x:=z] ∪ (γ \ {x}))) =α t where z is fresh     iff
   * t = λy.t' and y ∉ FV( s ([x:=z] ∪ (γ \ {x})) ) \ {z} and (s ([x:=z] ∪ (γ \ {x}))) [z:=y] =α t'
   * iff (since z is fresh) all the following hold:
   * - t = λy.t'
   * - y ∉ FV( γ(a) ) for any a ∈ FV(s) \ {x}
   * - s ([x:=y] ∪ (γ \ {x})) =α t'
   */
  public static MatchFailure extendMatchWithAbstraction(Term pattern, Term instance,
                                                        MutableSubstitution gamma) {
    if (!instance.isAbstraction()) {
      return new MatchFailure(Set.of(1), Set.of(3),
        "Abstraction ", pattern, " is not instantiated by ", instance, ".");
    }
    
    // ensure that the type of x is mapped to the type of y, and replace γ by γ'=[x:=y] ∪ (γ \ {x})
    Variable x = pattern.queryVariable();
    Variable y = instance.queryVariable();
    Term backup = gamma.get(x);
    if (backup == null) {
      if (!x.queryType().match(y.queryType(), gamma)) {
        return new MatchFailure(Set.of(1, 5), Set.of(3, 7),
          "Abstraction ", pattern, " is not instantiated by ", instance,
          " because the types of the abstraction variables do not match (", x.queryType(),
          " versus ", y.queryType(), ").");
      }
      gamma.extend(x, y);
    }
    else gamma.replace(x, y);

    // ensure that s γ' = t
    MatchFailure ret =
      extendMatch(pattern.queryAbstractionSubterm(), instance.queryAbstractionSubterm(), gamma);

    // restore γ to what it was before (any type extension to ensure the type of x matches the type
    // of y remain, and that is as it should be!
    if (backup == null) gamma.delete(x);
    else gamma.replace(x, backup);

    if (ret != null) return ret;

    // if we have not failed yet, check that y ∉ FV( γ(a) ) for any a ∈ FV(s) \ {x} = FV(λx.s)
    for (Replaceable z : pattern.queryFreeReplaceables()) {
      Term gammaz = gamma.get(z);
      if (gammaz != null && gammaz.queryFreeReplaceables().contains(y)) {
        return new MatchFailure(Set.of(1, 5), Set.of(3, 7),
          "Abstraction ", pattern, " is not instantiated by ", instance,
          " because the induced mapping [", z, " := ", gammaz, "] contains the binder variable of ",
          instance, ".");
      }
    }
    return null;
  }

}

