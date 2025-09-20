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
   * This method replaces each variable x in the term by get(x) (or leaves x alone if x is not
   * in our domain), and similarly replaces Z⟨s1,...,sk⟩ with gamma(Z) = λx1...xk.t by
   * t[x1:=s1 gamma,...,xk:=sk gamma]; the result is returned.
   *
   * Both the original term and the current substitution are unaltered, as they are in principle
   * immutable objects.  However, for the sake of efficiency, substituting does *temporarily*
   * alter the Substitution it when substituting lambda-expressions (as the binder is added to the
   * domain of the substitution and removed again after the substitution has been applied to the
   * subterm).  This may be relevant and require changing if Charlie is used in a concurrent way,
   * and could also be relevant if an exception occurs during substitution.  (However, this should
   * never be the case; there are no exceptions expected.)
   *
   * Note that the result of substituting is a term where all binders in lambdas are freshly
   * generated.
   */
  Term substitute(Term term);

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

  /** Creates an immutable substitution [x:=value] */
  public static Substitution of(Replaceable x, Term value) {
    return (new MutableSubstitution(x, value)).makeImmutable();
  }

  /** Creates an immutable substitution [x1:=s1,x2:=s2] */
  public static Substitution of(Replaceable x1, Term s1, Replaceable x2, Term s2) {
    MutableSubstitution ret = new MutableSubstitution(x1, s1);
    ret.extend(x2, s2);
    return ret.makeImmutable();
  }

  /** Creates an immutable substitution [x1:=s1,x2:=s2,x3:=s3] */
  public static Substitution of(Replaceable x1, Term s1, Replaceable x2, Term s2,
                                Replaceable x3, Term s3) {
    MutableSubstitution ret = new MutableSubstitution(x1, s1);
    ret.extend(x2, s2);
    ret.extend(x3, s3);
    return ret.makeImmutable();
  }
}

