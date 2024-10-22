/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.util;

import charlie.exceptions.NullStorageException;

import java.lang.Iterable;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

/**
 * This class provides a read-only set, with no null entries.
 * Functionality is much like java.util.Set, but only read functionality is provided, as write
 * functionality should not be used.
 * (Thus, unlike Guava's ImmutableSet type, it cannot be confused for a mutable Set.)
 */
public class FixedSet<T> implements Iterable<T> {
  private final Set<T> _myset;

  /**
   * Private constructor, because we should only be created through the builder or the
   * dedicated static construction functions.
   */
  FixedSet(Set<T> set) {
    _myset = set;
  }

  /** Create a fixed copy of the given set. */
  public static <T> FixedSet<T> copy(Set<T> args) {
    if (args == null) throw new NullStorageException("FixedSet", "set to be copied");
    Set<T> ret = args instanceof TreeSet ? new TreeSet<T>() : new HashSet<T>();
    for (T x : args) {
      if (x == null) throw new NullStorageException("FixedSet", "element in copy constructor");
      ret.add(x);
    }
    return new FixedSet<T>(ret);
  }

  public static <T> FixedSet<T>of() {
    return new FixedSet<T>(Set.of());
  }
  public static <T> FixedSet<T> of(T arg1) {
    if (arg1 == null) throw new NullStorageException("FixedSet", "element in unary constructor");
    return new FixedSet<T>(Set.of(arg1));
  }
  public static <T> FixedSet<T> of(T arg1, T arg2) {
    if (arg1 == null) throw new NullStorageException("FixedSet", "element 1 in biary constructor");
    if (arg2 == null) throw new NullStorageException("FixedSet", "element 2 in biary constructor");
    return new FixedSet<T>(Set.of(arg1, arg2));
  }
  /** Create the set of a given (fixed) series of arguments */
  @SafeVarargs
  public static <T> FixedSet<T>of(T ...args) {
    final HashSet<T> result = new HashSet<T>(args.length);
    for (T x : args) {
      if (x == null) throw new NullStorageException("FixedSet", "element in of constructor");
      result.add(x);
    }
    return new FixedSet<T>(result);
  }

  public boolean equals(FixedSet<T> other) { return _myset.equals(other._myset); }
  public boolean equals(Set<T> other) { return _myset.equals(other); }
  public boolean contains(T element) { return _myset.contains(element); }
  public int hashCode() { return _myset.hashCode(); }
  public boolean isEmpty() { return _myset.isEmpty(); }
  public Stream<T> parallelStream() { return _myset.parallelStream(); }
  public int size() { return _myset.size(); }
  public Stream<T> stream() { return _myset.stream(); }
  
  private class ImmutableIterator<T> implements Iterator<T> {
    Iterator<T> _mine;
    private ImmutableIterator(Iterator<T> mine) { _mine = mine; }
    public boolean hasNext() { return _mine.hasNext(); }
    public T next() { return _mine.next(); }
    // we explicitly do NOT provide remove
  }

  public Iterator<T> iterator() { return new ImmutableIterator<T>(_myset.iterator()); }

  /** Creates a Builder that generates a FixedSet functioning like a TreeSet */
  public static <T> Builder<T> treeBuilder() {
    return new Builder<T>(new TreeSet<T>());
  }

  /** Creates a Builder that generates a FixedSet functioning like a HashSet */
  public static <T> Builder<T> hashBuilder(int expectedSize) {
    return new Builder<T>(new HashSet<T>(expectedSize));
  }

  public static class Builder<T> {
    private Set<T> _internal;
    private Builder(Set<T> internal) { _internal = internal; }
    public void add(T element) {
      if (_internal == null) { throw new RuntimeException("Using builder that was already built!"); }
      if (element == null) throw new NullStorageException("FixedSet", "element in builder");
      _internal.add(element);
    }
    /** Builds the created set. Afterwards, this builder cannot be used anymore! */
    public FixedSet<T> build() {
      FixedSet<T> ret = new FixedSet<T>(_internal);
      _internal = null;
      return ret;
    }
  }
}
