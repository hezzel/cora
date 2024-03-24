/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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
import charlie.exceptions.ArityError;
import charlie.exceptions.NullStorageError;
import charlie.exceptions.TypingError;

/**
 * A substitution is a function that maps a finite set of variables/meta-variables (replaceables)
 * to terms of the same type.
 */
class Subst implements Substitution {
  private final HashMap<Replaceable,Term> _mapping;

  /** Creates an empty substitution, with empty domain. */
  Subst() {
    _mapping = new HashMap<Replaceable,Term>();
  }

  /**
   * Creates a substitution with a single key/value pair.
   * If key or value is null, then a NullStorageError is thrown; if the types of key and value are
   * not matched this results in a TypingError.
   */
  Subst(Replaceable key, Term value) {
    _mapping = new HashMap<Replaceable,Term>();
    extend(key, value);
  }

  /** @return the term that x is mapped to, or null if x is not mapped to anything */
  public Term get(Replaceable x) {
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
  public boolean extend(Replaceable key, Term value) {
    if (key == null) throw new NullStorageError("Subst", "key");
    if (value == null) throw new NullStorageError("Subst", "value");
    if (!key.queryType().equals(value.queryType())) {
      throw new TypingError("Subst", "extend", "value " + value.toString() + " assigned to key " +
        key.toString(), value.queryType().toString(), key.queryType().toString());
    }
    int a = key.queryArity();
    if (a > 0) {
      Term tmp = value;
      while (a > 0) {
        if (!tmp.isAbstraction()) throw new ArityError("Subst", "extend", "cannot add mapping " +
          key.toString() + " := " + value.toString() + " since " + key.toString() + " has arity " +
          a + ".");
        a--;
        tmp = tmp.queryAbstractionSubterm();
      }
    }
    if (_mapping.get(key) != null) return false;
    _mapping.put(key, value);
    return true;
  }

  /**
   * Adds the key/value pair to the substitution, replacing an existing pair for key if there is
   * one (in this case true is returned, in the alternative case false).
   */
  public boolean replace(Replaceable key, Term value) {
    boolean overriding = !extend(key, value);
    if (overriding) _mapping.put(key, value);
    return overriding;
  }

  /** Returns the set of variables which are mapped to something (possibly themselves). */
  public Set<Replaceable> domain() {
    return _mapping.keySet();
  }

  /** Remove the given key/value pair. */
  public void delete(Replaceable key) {
    _mapping.remove(key);
  }
}
