package cora.utils;

import java.util.Collection;
import java.util.Set;
import java.util.TreeMap;
import cora.exceptions.NullStorageError;

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
        throw new NullStorageError("LookupMap", "canont store a null value in a LookupMap");
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
