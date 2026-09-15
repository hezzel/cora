/**************************************************************************************************
 Copyright 2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.types;

import java.util.Collection;
import java.util.Iterator;
import java.util.TreeSet;

/**
 * A TVarSet is an immutable set of TVars, specialised with functions to easily (and efficiently)
 * add the type variables in any given type.
 */
public class TVarSet implements Iterable<TVar> {
  private final TreeSet<TVar> _elements;
  public static final TVarSet EMPTY = new TVarSet();

  /** Constructs the empty set */
  public TVarSet() {
    _elements = new TreeSet<TVar>();
  }

  /** Constructs the set with a copy of the given type variables. */
  public TVarSet(Collection<TVar> elems) {
    _elements = new TreeSet<TVar>(elems);
  }

  /** Returns the set containing all the type variables in the given type. */
  public static TVarSet of(Type type) {
    return EMPTY.add(type);
  }

  /** Returns whether the given type variable is an element of this set. */
  public boolean contains(TVar x) {
    return _elements.contains(x);
  }

  /** Returns the number of type variables in this set. */
  public int size() {
    return _elements.size();
  }

  /** Returns true if size() == 0 */
  public boolean isEmpty() {
    return _elements.isEmpty();
  }

  /** Returns an iterator over all type variables in the set. */
  public Iterator<TVar> iterator() {
    return _elements.iterator();
  }

  /**
   * Returns a copy of this set with all the type variables in the given type added.
   * If there is nothing to add (i.e., if all type variables in the given type already occur in
   * us), then this does not create a copy, but returns the current set directly.
   */
  public TVarSet add(Type type) {
    TVarSet ret = addVariablesIn(type, null);
    if (ret == null) return this;
    return ret;
  }

  /** Helper function for add(type). */
  private TVarSet addVariablesIn(Type type, TVarSet set) {
    if (type instanceof TVar alpha) {
      if (set == null) {
        if (_elements.contains(alpha)) return set;
        set = new TVarSet(_elements);
      }
      else if (set._elements.contains(alpha)) return set;
      set._elements.add(alpha);
    }
    else {
      for (int i = 1; i <= type.queryNumberSubtypes(); i++) {
        set = addVariablesIn(type.querySubtype(i), set);
      }
    }
    return set;
  }

  /** Returns a combination of the current set with the given set (not changing either). */
  public TVarSet combine(TVarSet other) {
    if (size() < other.size()) return other.combine(this);
    TVarSet ret = null;
    for (TVar alpha : other) {
      if (_elements.contains(alpha)) continue;
      if (ret == null) ret = new TVarSet(_elements);
      ret._elements.add(alpha);
    }
    if (ret == null) return this;
    return ret;
  }
  
  /** Only for debugging, not for printing to the user! */
  public String toString() {
    return _elements.toString();
  }
}
