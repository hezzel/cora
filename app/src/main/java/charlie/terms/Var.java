/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

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
import charlie.exceptions.IndexingError;
import charlie.exceptions.NullInitialisationError;
import charlie.types.Type;

/**
 * Non-binder variables are both used as parts of constraints, as generic expressions in terms, and
 * as open spots for matching in rules; this class represents all those kinds of variables.
 *
 * Variables have a name for printing purposes, but are not uniquely defined by it (distinct
 * variables may have the same name and type, although this will typically be avoided within a
 * single term).  Rather, variables are uniquely identified by an internally kept index (along with
 * their binder/non-binder status).  By construction, no non-binder variables with an index greater
 * than COUNTER can exist in the program.
 *
 * A non-binder variable is also a meta-variable with arity 0.
 */
class Var extends LeafTermInherit implements Variable, MetaVariable {
  private static int COUNTER = 0;
  private final String _name;
  private final int _index;

  /** Create a non-binder variable with the given name and type. */
  Var(String name, Type type) {
    super(type);
    _name = name;
    _index = COUNTER;
    COUNTER++;
    if (name == null) throw new NullInitialisationError("Var", "name");
    setVariables(new ReplaceableList(this));
  }

  /** Create a non-binder variable without a name; a name will be automatically generated. */
  Var(Type type) {
    super(type);
    _name = "X{" + COUNTER + "}";
    _index = COUNTER;
    COUNTER++;
    setVariables(new ReplaceableList(this));
  }

  /** @return true */
  public boolean isVariable() { return true; }

  /** @return true */
  public boolean isVarTerm() { return true; }

  /** @return true */
  public boolean isMetaApplication() { return true; }

  /** @return false */
  public boolean isBinderVariable() { return false; }

  /** @return true */
  public boolean isApplicative() { return true; }

  /** @return true if and only if the type is a theory type */
  public boolean isTheoryTerm() { return queryType().isTheoryType(); }

  /** @return 0 */
  public int queryArity() { return 0; }

  /** @return true if the type is base */
  public boolean isFirstOrder() {
    return queryType().isBaseType();
  }

  /** Returns the name this variable was set up with. */
  public String queryName() {
    return _name;
  }

  /** @return an integer uniquely identifying this non-binder variable */
  public int queryIndex() {
    return _index;
  }

  public int queryReplaceableKind() {
    return Replaceable.KIND_BASEVAR;
  }

  /** @return the type of this variable */
  public Type queryOutputType() {
    return queryType();
  }

  /** @throws IndexingError, since there are no arguments */
  public Type queryInputType(int index) {
    throw new IndexingError("Var", "queryInputType", index);
  }

  /** @return this */
  public Variable queryVariable() {
    return this;
  }

  /** @return this */
  public MetaVariable queryMetaVariable() {
    return this;
  }

  /** @return gamma(x) if the current variable is x and x in dom(gamma), otherwise just x */
  public Term substitute(Substitution gamma) {
    if (gamma == null) throw new NullPointerException("Substitution in Var::substitute");
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
    if (other == null) throw new NullPointerException("Matched term in Var::match");
    if (gamma == null) throw new NullPointerException("Substitution in Var::match");

    Term previous = gamma.get(this);
    
    if (previous == null) {
      if (!other.queryType().equals(queryType())) {
        return "Variable " + _name + " has a different type from " + other.toString() + ".";
      }
      gamma.extend(this, other);
      return null;
    }   
    else if (previous.equals(other)) return null;
    else return "Variable " + _name + " mapped both to " + previous.toString() + " and to " +
      other.toString() + ".";
  }

  /** Two variables are equal if and only if they are the same object. */
  public boolean equals(Variable other) {
    return other == this;
  }

  /** We are equal to another replaceable if and only if it is the same as us. */
  public boolean equals(Replaceable other) {
    return other == this;
  }

  /** Alpha-equality of a non-binder variable to another variable holds iff they are the same. */
  public boolean alphaEquals(Term term, Map<Variable,Integer> mu, Map<Variable,Integer> xi, int k) {
    return term.isVariable() && equals(term.queryVariable());
  }

  /** Implements a total ordering on replaceables using the kind, type and index. */
  public int compareTo(Replaceable other) {
    if (other == this) return 0;    // shortcut
    int d = other.queryReplaceableKind() - queryReplaceableKind();
    if (d != 0) return d;
    if (_index < other.queryIndex()) return -1; 
    if (_index > other.queryIndex()) return 1;
    return queryType().toString().compareTo(other.queryType().toString());
  }
}
