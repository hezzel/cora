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
 * A ReplaceableList is an immutable set of Replaceables.
 * The names used within a replaceable list are not necessarily unique.
 */
public class ReplaceableList implements Iterable<Replaceable> {
  private final TreeSet<Replaceable> _elements;
  public static final ReplaceableList EMPTY = new ReplaceableList();

  /** Constructs the empty list */
  public ReplaceableList() {
    _elements = new TreeSet<Replaceable>();
  }

  /** Constructs the list with just the given replaceable. */
  public ReplaceableList(Replaceable x) {
    _elements = new TreeSet<Replaceable>();
    _elements.add(x);
  }

  /** Constructs the list with a copy of the given replaceables. */
  public ReplaceableList(Collection<Replaceable> elems) {
    _elements = new TreeSet<Replaceable>(elems);
  }

  /** Returns whether the given replaceable is an element of this list. */
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

  /** Returns a copy of this list with the given element added. */
  public ReplaceableList add(Replaceable x) {
    if (_elements.contains(x)) return this;
    ReplaceableList ret = new ReplaceableList(_elements);
    ret._elements.add(x);
    return ret;
  }

  /** Returns a copy of this list with the given replaceable removed. */
  public ReplaceableList remove(Replaceable x) {
    if (!_elements.contains(x)) return this;
    ReplaceableList ret = new ReplaceableList(_elements);
    ret._elements.remove(x);
    return ret;
  }

  /** Returns a combination of the current list with the given list. */
  public ReplaceableList combine(ReplaceableList other) {
    if (size() < other.size()) return other.combine(this);
    ReplaceableList ret = null;
    for (Replaceable x : other) {
      if (_elements.contains(x)) continue;
      if (ret == null) ret = new ReplaceableList(_elements);
      ret._elements.add(x);
    }
    if (ret == null) return this;
    return ret;
  }

  /** Returns the set of Replaceables that occur both in this list and the given iterable. */
  public TreeSet<Replaceable> getOverlap(Iterable<Replaceable> other) {
    TreeSet<Replaceable> ret = new TreeSet<Replaceable>();
    for (Replaceable x : other) {
      if (_elements.contains(x)) ret.add(x);
    }
    return ret;
  }
}

