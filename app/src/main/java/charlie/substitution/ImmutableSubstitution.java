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
 * An ImmutableSubstitution is a Substitution that cannot be altered by objects that it is given to.
 * The underlying MutableSubstitution can still be altered by its owner, but by using an
 * immutability wrapper, one may ensure that other objects can only use it as intended.
 */
public class ImmutableSubstitution implements Substitution {
  private MutableSubstitution _wrapped;

  // the constructor is not public, since we should be created through makeImmutable()
  ImmutableSubstitution(MutableSubstitution wrapme) { _wrapped = wrapme; }
  
  public Term get(Replaceable x) { return _wrapped.get(x); }
  public Term getReplacement(Replaceable x) { return _wrapped.getReplacement(x); }
  public Term apply(Term term) { return _wrapped.apply(term); }
  public Set<Replaceable> domain() { return _wrapped.domain(); }
  public MutableSubstitution copy() { return _wrapped.copy(); }
  public Substitution makeImmutable() { return this; }
  public String toString() { return _wrapped.toString(); }
}

