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

import java.util.Collection;
import java.util.Set;
import java.util.TreeMap;
import charlie.exceptions.NullStorageException;

/**
 * This class provides a read-only mapping from strings to a given type, with no null entries.
 * Functionality is much like java.util.Map, but only read functionality is provided, as write
 * functionality should not be used.
 * (Thus, unlike Guava's ImmutableMap type, it cannot be confused for a mutable Map.)
 */
public class LookupMap<T> {
  TreeMap<String,T> _mymap;

  public boolean containsKey(String key) { return _mymap.containsKey(key); }
  public T get(String key) { return _mymap.get(key); }
  public boolean isEmpty() { return _mymap.isEmpty(); }
  public int size() { return _mymap.size(); }
  public Set<String> keySet() { return _mymap.keySet(); }
  public Collection<T> values() { return _mymap.values(); }
  public String toString() { return _mymap.toString(); }

  /** Private constructor, because we should only be created through the builder. */
  LookupMap(TreeMap<String,T> map) {
    _mymap = map;
  }

  public static <T> LookupMap empty() { return new LookupMap<T>(new TreeMap<String,T>()); }

  public static class Builder<T> {
    private TreeMap<String,T> _internal;

    public Builder() {
      _internal = new TreeMap<String,T>();
    }

    public boolean containsKey(String key) { return _internal.containsKey(key); }
    public T get(String key) { return _internal.get(key); }
    public void put(String key, T value) {
      _internal.put(key, value);
      if (value == null) {
        throw new NullStorageException("LookupMap", "cannot store a null value in a LookupMap");
      }
    }

    /** Builds the created lookup map. Afterwards, this builder cannot be used anymore! */
    public LookupMap<T> build() {
      LookupMap<T> ret = new LookupMap(_internal);
      _internal = null;
      return ret;
    }
  }
}
