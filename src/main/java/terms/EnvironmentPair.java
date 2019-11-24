/**************************************************************************************************
 Copyright 2019 Cynthia Kop

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

import java.util.List;
import java.util.TreeSet;
import cora.exceptions.IllegalTermError;
import cora.exceptions.NullInitialisationError;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Environment;

/**
 * An EnvironmentPair couples a set of free and a set of bound variables, and has functionality to
 * merge environments and move variables around while throwing an IllegalTermError if a variable is
 * encountered in both environments.
 */
public class EnvironmentPair {
  private Environment _freeVars;
  private Environment _boundVars;
  private static EnvironmentPair _emptyPair = new EnvironmentPair();

  /** Creates an environment pair with no bound or free variables. */
  private EnvironmentPair() {
    _freeVars = new Env();
    _boundVars = new Env();
  }

  /** Creates an environment pair with a single free variable (but no bound ones). */
  public EnvironmentPair(Variable x) {
    _freeVars = new Env(x);
    _boundVars = new Env();
  }

  /**
   * Creates an environment pair with the given free and bound variables.
   * WARNING: this function does not check that there are no overlaps between free and bound
   * variables! This should be guaranteed by the function that creates the environment pair.
   */
  public EnvironmentPair(Environment frees, Environment bounds) {
    if (frees == null) throw new NullInitialisationError("EnvironmentPair", "frees is null!");
    if (bounds == null) throw new NullInitialisationError("EnvironmentPair", "bounds is null!");

    _freeVars = frees;
    _boundVars = bounds;
  }

  /** @return an EnvironmentPair with no free of bound variables */
  public static EnvironmentPair emptyPair() {
    return _emptyPair;
  }

  /** Adds the given variable as a free one and returns the result. */
  public EnvironmentPair addFreeVar(Variable x) {
    if (_freeVars.contains(x)) return this;

    if (_boundVars.contains(x)) {
      throw new IllegalTermError("Variable " + x.queryName() + " occurs both free and bound!");
    }
    return new EnvironmentPair(_freeVars.extend(x), _boundVars);
  }

  /** Adds the given variable as a bound one and returns the result. */
  public EnvironmentPair addBoundVar(Variable x) {
    if (_boundVars.contains(x)) return this;

    if (_freeVars.contains(x)) {
      throw new IllegalTermError("Variable " + x.queryName() + " occurs both bound and free!");
    }
    return new EnvironmentPair(_freeVars, _boundVars.extend(x));
  }

  /**
   * Removes the given variable from the free vars, adds it to the bound ones, and returns the
   * result.
   * This error-checks that the given variable was not already marked as bound!
   */
  public EnvironmentPair markFreeVarAsBound(Variable x) {
    if (_boundVars.contains(x)) {
      throw new IllegalTermError("Trying to mark variable " + x.queryName() + " as bound when " +
                                 "it was already so!");
    }
    Environment newfrees = (_freeVars.contains(x) ? _freeVars.remove(x) : _freeVars);
    Environment newbounds = _boundVars.extend(x);
    return new EnvironmentPair(newfrees, newbounds);
  }

  /** Returns the free variables in this pair. */
  public Environment freeVars() { return _freeVars; }

  /** Returns the bound variables in this pair. */
  public Environment boundVars() { return _boundVars; }
  
  /** Throws an IllegalTermError if the environments have any shared variables. */
  private static void checkConsistency(Environment freeEnv, Environment boundEnv) {
    for (Variable x : freeEnv) {
      if (boundEnv.contains(x)) {
        throw new IllegalTermError("Variable " + x.toString() + " occurs both bound and free in " +
          "merge.");
      }
    }
  }

  /**
   * Returns an EnvironmentPair that merges all the given pairs.
   * @throws IllegalTermError if this results in any variable being in both freeVars and boundVars.
   * 
   * This function has been optimised to reuse existing environments / environment pairs as much as
   * possible, so that trivial merges do not lead to the allocation of additional memory.  This is
   * done because environment pairs are stored at all levels in a term, which might cause very high
   * memory usage for larger terms if done carelessly.
   */
  public static EnvironmentPair mergeAll(List<EnvironmentPair> lst) {
    // nothing to merge => return the empty environment
    if (lst.size() == 0) return _emptyPair;

    // just one element => use that
    if (lst.size() == 1) return lst.get(0);

    // there's a most general pair => return that one
    EnvironmentPair ret = findPairThatContainsAll(lst);
    if (ret != null) return ret;
    
    // find optimal sets of free and bound variables, possibly through reuse, and couple them in an
    // EnvironmentPair
    Environment frees = findEnvThatContainsAll(lst, true);
    if (frees == null) frees = createMergedEnvironment(lst, true);
    Environment bounds = findEnvThatContainsAll(lst, false);
    if (bounds == null) bounds = createMergedEnvironment(lst, false);
    checkConsistency(frees, bounds);
    return new EnvironmentPair(frees, bounds);
  }

  /**
   * If the given list contains an environment pair that includes all others, this pair is
   * returned; otherwise null is returned.
   */
  private static EnvironmentPair findPairThatContainsAll(List<EnvironmentPair> lst) {
    int largestFree = 0, largestBound = 0;
    int best = 0;
    for (int i = 0; i < lst.size(); i++) {
      int f = lst.get(i).freeVars().size();
      int b = lst.get(i).boundVars().size();
      if (f >= largestFree && b >= largestBound) { largestFree = f; largestBound = b; best = i; }
      if (f > largestFree || b > largestBound) return null;
    }

    for (int i = 0; i < lst.size(); i++) {
      if (i == best) continue;
      if (!lst.get(best).freeVars().containsAll(lst.get(i).freeVars())) return null;
      if (!lst.get(best).boundVars().containsAll(lst.get(i).boundVars())) return null;
    }

    return lst.get(best);
  }

  /**
   * If free is true, then this goes through freeVars() for every pair in the given list, and if
   * there is one that contains all the variables occurring in any freeVars() environment in the
   * list, it returns that Environment; if no such element exists, null is returned instead.
   * If free is false, the same is done with boundVars() instead.
   */
  private static Environment findEnvThatContainsAll(List<EnvironmentPair> lst, boolean free) {
    int largest = 0;
    Environment best = null;
    for (int i = 0; i < lst.size(); i++) {
      Environment env = (free ? lst.get(i).freeVars() : lst.get(i).boundVars());
      if (best == null || env.size() > largest) {
        largest = env.size();
        best = env;
      }
    }

    for (EnvironmentPair p : lst) {
      Environment other = (free ? p.freeVars() : p.boundVars());
      if (other == best) continue; // pointer equality to avoid trivial comparison
      if (!best.containsAll(other)) return null;
    }

    return best;
  }

  /**
   * If free is true, this creates a new Environment that contains all variables occurring in
   * freeVars() for any element of lst; if free is false, it does the same for boundVars().
   */
  private static Environment createMergedEnvironment(List<EnvironmentPair> lst, boolean free) {
    TreeSet<Variable> vars = new TreeSet<Variable>();
    for (EnvironmentPair p : lst) {
      Environment other = (free ? p.freeVars() : p.boundVars());
      for (Variable x : other) vars.add(x);
    }
    return new Env(vars);
  }
}

