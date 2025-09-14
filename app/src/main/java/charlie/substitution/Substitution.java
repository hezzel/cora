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

import java.util.Set;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.Term;

/**
 * A substitution is a function that maps a finite set of replaceables to terms of the same type.
 * Substitutions can be both mutable and immutable.
 */
public interface Substitution {
  /** Returns the Term that x is mapped to, or null if x is not mapped to anything. */
  Term get(Replaceable x);

  /**
   * Returns the Term that x is mapped to, if anything, and if x is not mapped to anything then this
   * returns either x itself (if x is a variable) or λy1...yn.x[y1,...,yn] (if x is a meta-variable of
   * arity n).
   */
  Term getReplacement(Replaceable x);

  /**
   * Applies the current substitution to the given term and returns the result.
   */
  Term apply(Term term);

  /**
   * Returns the set of replaceables which are mapped to a term, including those which are mapped
   * to themselves.
   */
  Set<Replaceable> domain();

  /** Returns a copy of the current substitution. */
  public MutableSubstitution copy();

  /**
   * Puts an immutable wrapper around the present Substitution.  Beware: changing the present
   * renaming can still cause mutations to the result; only the objects that receive the immutable
   * wrapper cannot cause alterations to either it or the underlying Renaming.
   */
  public Substitution makeImmutable();
}

