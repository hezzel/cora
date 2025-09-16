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

package charlie.substitution;

import java.util.ArrayList;
import java.util.TreeSet;
import charlie.util.UserException;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.MetaVariable;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TermFactory;

/**
 * The matcher is a static class that is used to match a pattern against another term.
 */
public class Matcher {
  public static class MatchFailure extends UserException {
    public MatchFailure(Object ...args) { super(args); }
    public String toString() { return getMessage(); }
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
   * If it is not possible, then an appropriate FailureReason is returned.
   */
  public static MatchFailure extendMatch(Term pattern, Term instance, MutableSubstitution subst) {
    if (pattern.isVariable()) {
      return extendMatchWithVariable(pattern.queryVariable(), instance, subst);
    }
    else if (pattern.isMetaApplication()) {
      return extendMatchWithMeta(pattern, instance, subst);
    }
    else if (pattern.isConstant()) {
      return checkMatchWithConstant(pattern, instance);
    }
    else if (pattern.isApplication()) {
      return extendMatchWithApplication(pattern, instance, subst);
    }   
    else if (pattern.isTuple()) {
      return extendMatchWithTuple(pattern, instance, subst);
    }   
    else if (pattern.isAbstraction()) {
      return extendMatchWithAbstraction(pattern, instance, subst);
    }   
    else throw new IllegalArgumentException("Matcher::extendMatch called with a term that does " +
      "not have any of the standard term shapes!");
  }

  private static MatchFailure extendMatchWithVariable(Variable x, Term instance,
                                                      MutableSubstitution gamma) {
    Term previous = gamma.get(x);
    if (previous == null) {
      if (!instance.queryType().equals(x.queryType())) {
        return new MatchFailure("Variable ", x, " has a different type from ", instance, ".");
      }   
      gamma.extend(x, instance);
      return null;
    }   
    if (previous.equals(instance)) return null;
    return new MatchFailure("Variable ", x, " is mapped both to ", previous, " and to ",
                            instance, ".");
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
    // check if the type matches (and perhaps a previous match), and add the mapping!
    MetaVariable metavar = metaApp.queryMetaVariable();
    Term previous = gamma.get(metavar);
    if (previous == null) {
      if (!instance.queryType().equals(metaApp.queryType())) {
        return new MatchFailure("Cannot match ", metaApp, " against ", instance, 
                                " as types do not match.");
      }   
      gamma.extend(metavar, ret);
      return null;
    }   
    if (previous.equals(ret)) return null;
    return new MatchFailure("Meta-variable ", metavar, " is mapped to both " , previous, 
                            " and to ", ret, ".");
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
    for (int i = 1; i <= metaApp.numberMetaArguments(); i++) {
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

  private static MatchFailure checkMatchWithConstant(Term symbol, Term instance) {
    if (symbol.equals(instance)) return null;
    return new MatchFailure("Constant ", symbol, " is not instantiated by ", instance, ".");
  }

  private static MatchFailure extendMatchWithApplication(Term pattern, Term instance,
                                                         MutableSubstitution gamma) {
    if (!instance.isApplication()) {
      return new MatchFailure("The term ", instance, " does not instantiate ", pattern, " as it " +
        "is not an application.");
    }
    if (instance.numberArguments() < pattern.numberArguments()) {
      return new MatchFailure("The term ", instance, " does not instantiate ", pattern, " as it " +
        "has too few arguments.");
    }
    int i = instance.numberArguments();
    int j = pattern.numberArguments();
    for (; j > 0; i--, j--) {
      Term patsub = pattern.queryArgument(j);
      Term inssub = instance.queryArgument(i);
      MatchFailure warning = extendMatch(patsub, inssub, gamma);
      if (warning != null) return warning;
    }
    return extendMatch(pattern.queryHead(), instance.queryImmediateHeadSubterm(i), gamma);
  }

  private static MatchFailure extendMatchWithTuple(Term tuple, Term instance,
                                                   MutableSubstitution gamma) {
    if (!instance.isTuple()) {
      return new MatchFailure("The term ", instance, " does not instantiate ", tuple,
        " as it is not a tuple term.");
    }
    if (tuple.numberTupleArguments() != instance.numberTupleArguments()) {
      return new MatchFailure("The term ", instance, " does not instantiate ", tuple,
        " as the tuple sizes are not the same.");
    }   
    for (int i = 1; i <= tuple.numberTupleArguments(); i++) {
      MatchFailure warning = extendMatch(tuple.queryTupleArgument(i),
                                         instance.queryTupleArgument(i), gamma);
      if (warning != null) return warning;
    }
    return null;
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
      return new MatchFailure("Abstraction ", pattern, " is not instantiated by ", instance, ".");
    }
    Variable x = pattern.queryVariable();
    Variable y = instance.queryVariable();

    Term backup = gamma.get(x);
    if (backup == null) gamma.extend(x, y);
    else gamma.replace(x, y);
    MatchFailure ret =
      extendMatch(pattern.queryAbstractionSubterm(), instance.queryAbstractionSubterm(), gamma);
    if (backup == null) gamma.delete(x);
    else gamma.replace(x, backup);

    if (ret != null) return ret;

    for (Replaceable z : pattern.freeReplaceables()) {
      Term gammaz = gamma.get(z);
      if (gammaz != null && gammaz.freeReplaceables().contains(y)) {
        return new MatchFailure("Abstraction ", pattern, " is not instantiated by ", instance,
          " because the induced mapping [", z, " := ", gammaz, "] contains the binder variable of ",
          instance, ".");
      }
    }
    return null;
  }

}

