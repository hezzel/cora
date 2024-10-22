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
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;

/**
 * This class provides a read-only list, with no null entries.
 * Functionality is much like java.util.List, but only read functionality is provided, as write
 * functionality should not be used.
 * (Thus, unlike Guava's ImmutableList type, it cannot be confused for a mutable List.)
 */
public class FixedList<T> implements Iterable<T> {
  private final ArrayList<T> _mylist;

  /**
   * Private constructor, because we should only be created through the builder or the
   * dedicated static construction functions.
   */
  FixedList(ArrayList<T> lst) {
    _mylist = lst;
  }

  /** Create a fixed copy of the given list */
  public static <T> FixedList<T> copy(List<T> args) {
    if (args == null) throw new NullStorageException("FixedList", "list to be copied");
    final ArrayList<T> result = new ArrayList<T>(args.size());
    for (T x : args) {
      if (x == null) throw new NullStorageException("FixedList", "element in copy constructor");
      result.add(x);
    }
    return new FixedList<T>(result);
  }

  public static <T> FixedList<T>of() {
    return new FixedList<T>(new ArrayList<T>(0));
  }
  public static <T> FixedList<T> of(T arg1) {
    final ArrayList<T> result = new ArrayList<T>(1);
    if (arg1 == null) throw new NullStorageException("FixedList", "element in unary constructor");
    result.add(arg1);
    return new FixedList<T>(result);
  }
  public static <T> FixedList<T> of(T arg1, T arg2) {
    final ArrayList<T> result = new ArrayList<T>(2);
    if (arg1 == null) throw new NullStorageException("FixedList", "element 1 in biary constructor");
    if (arg2 == null) throw new NullStorageException("FixedList", "element 2 in biary constructor");
    result.add(arg1);
    result.add(arg2);
    return new FixedList<T>(result);
  }
  /** Create the list of a given (fixed) series of arguments */
  @SafeVarargs
  public static <T> FixedList<T>of(T ...args) {
    final ArrayList<T> result = new ArrayList<T>(args.length);
    for (T x : args) {
      if (x == null) throw new NullStorageException("FixedList", "element in of constructor");
      result.add(x);
    }
    return new FixedList<T>(result);
  }

  public boolean equals(FixedList<T> other) { return _mylist.equals(other._mylist); }
  public boolean equals(List<T> other) { return _mylist.equals(other); }
  public T get(int index) { return _mylist.get(index); }
  public int hashCode() { return _mylist.hashCode(); }
  public boolean isEmpty() { return _mylist.isEmpty(); }
  public Stream<T> parallelStream() { return _mylist.parallelStream(); }
  public int size() { return _mylist.size(); }
  public Stream<T> stream() { return _mylist.stream(); }
  
  private class ImmutableIterator<T> implements Iterator<T> {
    Iterator<T> _mine;
    private ImmutableIterator(Iterator<T> mine) { _mine = mine; }
    public boolean hasNext() { return _mine.hasNext(); }
    public T next() { return _mine.next(); }
    // we explicitly do NOT provide remove
  }

  public Iterator<T> iterator() { return new ImmutableIterator<T>(_mylist.iterator()); }

  public static class Builder<T> {
    private ArrayList<T> _internal;
    public Builder() { _internal = new ArrayList<T>(); }
    public Builder(int expectedSize) { _internal = new ArrayList<T>(expectedSize); }
    public void add(T element) {
      if (_internal == null) { throw new RuntimeException("Using builder that was already built!"); }
      if (element == null) throw new NullStorageException("FixedList", "element in builder");
      _internal.add(element);
    }
    /** Builds the created list. Afterwards, this builder cannot be used anymore! */
    public FixedList<T> build() {
      FixedList<T> ret = new FixedList<T>(_internal);
      _internal = null;
      return ret;
    }
  }
}
