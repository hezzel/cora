/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms.replaceable;

import java.util.Collection;
import java.util.Iterator;
import java.util.TreeSet;

/**
 * A ReplaceableSet is an immutable set of Replaceables.
 * The names used within a replaceable set are not necessarily unique.
 */
public class ReplaceableSet implements Iterable<Replaceable> {
  private final TreeSet<Replaceable> _elements;
  public static final ReplaceableSet EMPTY = new ReplaceableSet();

  /** Constructs the empty set */
  public ReplaceableSet() {
    _elements = new TreeSet<Replaceable>();
  }

  /** Constructs the set with just the given replaceable. */
  public ReplaceableSet(Replaceable x) {
    _elements = new TreeSet<Replaceable>();
    _elements.add(x);
  }

  /** Constructs the set with a copy of the given replaceables. */
  public ReplaceableSet(Collection<Replaceable> elems) {
    _elements = new TreeSet<Replaceable>(elems);
  }

  /** Returns whether the given replaceable is an element of this set. */
  public boolean contains(Replaceable x) {
    return _elements.contains(x);
  }

  /** Returns the number of replaceables in this environment. */
  public int size() {
    return _elements.size();
  }

  /** Returns an iterator over all replaceables in the environment. */
  public Iterator<Replaceable> iterator() {
    return _elements.iterator();
  }

  /** Returns a copy of this set with the given element added. */
  public ReplaceableSet add(Replaceable x) {
    if (_elements.contains(x)) return this;
    ReplaceableSet ret = new ReplaceableSet(_elements);
    ret._elements.add(x);
    return ret;
  }

  /** Returns a copy of this set with the given replaceable removed. */
  public ReplaceableSet remove(Replaceable x) {
    if (!_elements.contains(x)) return this;
    ReplaceableSet ret = new ReplaceableSet(_elements);
    ret._elements.remove(x);
    return ret;
  }

  /** Returns a combination of the current set with the given set. */
  public ReplaceableSet combine(ReplaceableSet other) {
    if (size() < other.size()) return other.combine(this);
    ReplaceableSet ret = null;
    for (Replaceable x : other) {
      if (_elements.contains(x)) continue;
      if (ret == null) ret = new ReplaceableSet(_elements);
      ret._elements.add(x);
    }
    if (ret == null) return this;
    return ret;
  }

  /** Returns the set of Replaceables that occur both in this set and the given iterable. */
  public TreeSet<Replaceable> getOverlap(Iterable<Replaceable> other) {
    TreeSet<Replaceable> ret = new TreeSet<Replaceable>();
    for (Replaceable x : other) {
      if (_elements.contains(x)) ret.add(x);
    }
    return ret;
  }
}
