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

import java.util.HashMap;
import java.util.Set;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Substitution;
import cora.exceptions.NullStorageError;
import cora.exceptions.TypingError;

/**
 * A substitution is a function that maps a finite set of variables to terms of the same type.
 */
public class Subst implements Substitution {
  private HashMap<Variable,Term> _mapping;

  /** Creates an empty substitution, with empty domain. */
  public Subst() {
    _mapping = new HashMap<Variable,Term>();
  }

  /**
   * Creates a substitution with a single key/value pair.
   * If key or value is null, then a NullStorageError is thrown; if the types of key and value are
   * not matched this results in a TypingError.
   */
  public Subst(Variable key, Term value) {
    _mapping = new HashMap<Variable,Term>();
    extend(key, value);
  }

  /** @return the term that x is mapped to, or null if x is not mapped to anything */
  public Term get(Variable x) {
    return _mapping.get(x);
  }

  /**
   * Returns the Term that x is mapped to; if x is not in the domain, then the term corresponding
   * to x is returned instead.
   */
  public Term getReplacement(Variable x) {
    Term ret = _mapping.get(x);
    if (ret == null) return x;
    else return ret;
  }

  /**
   * Adds the key/value pair to the substitution.
   * This will return false and do nothing if there is an existing value for the key.
   */
  public boolean extend(Variable key, Term value) {
    if (key == null) throw new NullStorageError("Subst", "key");
    if (value == null) throw new NullStorageError("Subst", "value");
    if (!key.queryType().equals(value.queryType())) {
      throw new TypingError("Subst", "extend", "value " + value.toString() + " assigned to key " +
        key.toString(), value.queryType().toString(), key.queryType().toString());
    }
    if (_mapping.get(key) != null) return false;
    _mapping.put(key, value);
    return true;
  }

  /**
   * Adds the key/value pair to the substitution, replacing an existing pair for key if there is
   * one (in this case true is returned, in the alternative case false).
   */
  public boolean replace(Variable key, Term value) {
    boolean overriding = !extend(key, value);
    if (overriding) _mapping.put(key, value);
    return overriding;
  }

  /** Returns the set of variables which are mapped to something (possibly themselves). */
  public Set<Variable> domain() {
    return _mapping.keySet();
  }

  /** Remove the given key/value pair. */
  public void delete(Variable key) {
    _mapping.remove(key);
  }
}

