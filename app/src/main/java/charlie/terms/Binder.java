/**************************************************************************************************
 Copyright 2019--2025 Cynthia Kop

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

import java.util.Map;
import charlie.exceptions.InappropriatePatternDataException;
import charlie.util.NullStorageException;
import charlie.types.Type;

/**
 * Binders are variables in Vbinder: variables that are only meant to be used as binders in an
 * abstraction (and the corresponding occurrences in the term), not for matching purposes.
 * Like all variables, Binders have a name for printing purposes, but are not in any way defined by
 * it; variables are likely to be renamed while printing, with the basic name only used as a
 * suggestion for what the printed name should look like.  Hence, binder variables can have the
 * same name and type, but still be unequal.  Rather, they are uniquely identified by an internally
 * kept index.  By construction, no binder variables with an index greater than COUNTER can exist
 * in the program.
 */
class Binder extends LeafTermInherit implements Variable {
  private static int COUNTER = 0;
  private final String _name;
  private final int _index;

  /** Create a binder variable with the given name and type. */
  Binder(String name, Type type) {
    super(type);
    _name = name;
    _index = COUNTER;
    COUNTER++;
    if (name == null) throw new NullStorageException("Binder", "name");
    setVariables(new ReplaceableList(this));
  }

  /** Create a binder variable without a name; a name will be automatically generated. */
  Binder(Type type) {
    super(type);
    _name = "x{" + COUNTER + "}";
    _index = COUNTER;
    COUNTER++;
  }

  /** @return true */
  public boolean isVariable() { return true; }

  /** @return true */
  public boolean isVarTerm() { return true; }

  /** @return false */
  public boolean isMetaApplication() { return false; }

  /** @return true */
  public boolean isBinderVariable() { return true; }

  /** @return false (binder variables do not occur in applicative terms) */
  public boolean isApplicative() { return false; }

  /** @return false (binder variables do not occur in first-order terms) */
  public boolean isFirstOrder() { return false; }

  /** @return true if and only if the type is a theory type */
  public boolean isTheoryTerm() { return queryType().isTheoryType(); }

  /** Returns the name this variable was set up with. */
  public String queryName() {
    return _name;
  }

  /** @return KIND_BINDER */
  public int queryReplaceableKind() {
    return Replaceable.KIND_BINDER;
  }

  /** @return an integer uniquely identifying this binder variable */
  public int queryIndex() {
    return _index;
  }

  /** @return 0, since only meta-variables have an arity */
  public int queryArity() {
    return 0;
  }

  /** @return this */
  public Variable queryVariable() {
    return this;
  }

  /** @throws InappropriatePatternDataException, as a binder variable cannot be a meta-variable */
  public MetaVariable queryMetaVariable() {
    throw new InappropriatePatternDataException("Binder", "queryMetaVariable",
      "meta-variable applications");
  }

  /** @return gamma(x) if the current variable is x and x in dom(gamma), otherwise just x */
  public Term substitute(Substitution gamma) {
    if (gamma == null) throw new NullPointerException("Substitution in Binder::substitute");
    return gamma.getReplacement(this);
  }

  /** 
   * This method updates gamma by adding the extension from x to the given other term, if x is not
   * yet mapped to anything.
   * If this works, then null is returned.
   * If x is already mapped to the given other term, then nothing is done but null is returned.
   * If x is mapped to a different term, then an explanation of the match failure is returned.
   * If other or gamma is null, then a NullPointerException is thrown instead.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullPointerException("Other term in Binder::match");
    if (gamma == null) throw new NullPointerException("Substitution in Binder::match");

    Term previous = gamma.get(this);
    
    if (previous == null) {
      if (!other.queryType().equals(queryType())) {
        return "Binder " + _name + " has a different type from " + other.toString() + ".";
      }
      gamma.extend(this, other);
      return null;
    }   
    else if (previous.equals(other)) return null;
    else return "Binder " + _name + " mapped both to " + previous.toString() + " and to " +
      other.toString() + ".";
  }

  /**
   * Alpha-equality of a binder to another binder holds if either mu[this] = xi[that], or both
   * mu[this] and xi[that] are undefined and they are the same Variable.
   */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    if (!term.isVariable()) return false;
    if (mu.containsKey(this)) return mu.get(this).equals(xi.get(term.queryVariable()));
    else if (xi.containsKey(term.queryVariable())) return false;
    return equals(term.queryVariable());
  }

  /** Implements a total ordering on replaceables using the kind, index and type. */
  public int compareTo(Replaceable other) {
    if (other == this) return 0;  // shortcut
    int d = other.queryReplaceableKind() - queryReplaceableKind();
    if (d != 0) return d;
    if (_index < other.queryIndex()) return -1;
    if (_index > other.queryIndex()) return 1;
    return queryType().toString().compareTo(other.queryType().toString());
  }

  /** Shortcut: two replaceables are equal if and only if they are the same object. */
  public boolean equals(Replaceable other) {
    return other == this;
  }

  /** Shortcut: two variables are equal if and only if they are the same object. */
  public boolean equals(Variable other) {
    return other == this;
  }

  /** Returns a hashcode that (uniquely) identifies this Binder */
  public int hashCode(Map<Variable,Integer> mu) {
    if (mu != null && mu.containsKey(this)) return 3 * mu.get(this) + 1;
    return 3 * _index + 1;
  }
}
