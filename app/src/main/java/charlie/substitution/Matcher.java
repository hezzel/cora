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
/*
    else if (term.isConstant()) return term;
    else if (term.isApplication()) {
      return applyToApplication(term.queryHead(), term.queryArguments());
    }   
    else if (term.isTuple()) {
      return applyToTuple(term.queryTupleArguments());
    }   
    else if (term.isAbstraction()) {
      return applyToAbstraction(term.queryVariable(), term.queryAbstractionSubterm());
    }   
*/
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
}

