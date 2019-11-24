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
import java.util.ArrayList;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Environment;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.VariableNamer;

/**
 * A TermInherit supplies default functionality for all instances of Term.
 * This is the functionality that calls other functions in Term to for instance build up a
 * substitution or environment.
 */
abstract class TermInherit {
  private Environment _varsCache = null;

  abstract Environment allVars();
  abstract String match(Term other, Substitution gamma);
  abstract boolean equals(Term other);
  abstract Term apply(List<Term> args);
  abstract String toString(VariableNamer namer);

  /**
   * Calling this sets up the free variable cache.  It may be done at the end of a constructor, but
   * if not, it will automatically be called when freeVars() is first requested.
   */
  protected void initiateVars() {
    _varsCache = allVars();
  }

  /** Returns the set of all variables occurring freely in the current term. */
  public Environment freeVars() {
    if (_varsCache == null) initiateVars();
    return _varsCache;
  }

  /** Applies the current term (with functional type) to other. */
  public Term apply(Term other) {
    List<Term> args = new ArrayList<Term>();
    args.add(other);
    return apply(args);
  }

  /** Same as match(other, subst), but it creates a fresh substitution and returns the result. */
  public Substitution match(Term other) {
    Substitution gamma = new Subst();
    if (match(other, gamma) == null) return gamma;
    return null;
  }

  /** This method verifies equality to another Term. */
  public boolean equals(Object other) {
    if (other instanceof Term) return equals((Term)other);
    return false;
  }

  /**
   * This method returns a string representation of the current term, where variables are renamed
   * so that each variable has a unique name.
   */
  public String toPrettyString() {
    return toString(new CleverVariableNamer());
  }
}

