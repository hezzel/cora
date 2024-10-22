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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.List;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;

class FixedSetTest {
  @Test
  public void testCreateCopy() {
    TreeSet<String> tset = new TreeSet<String>();
    tset.add("Hello");
    tset.add("there");
    tset.add("World");
    FixedSet<String> fset = FixedSet.<String>copy(tset);
    assertTrue(fset.size() == 3);
    assertTrue(fset.equals(tset));
    assertTrue(fset.hashCode() == tset.hashCode());
    assertTrue(fset.contains("Hello"));
    assertTrue(fset.contains("there"));
    assertTrue(fset.contains("World"));
    tset.remove("there");
    tset.add("There");
    assertFalse(fset.contains("There"));
    assertTrue(fset.contains("there"));
  }

  @Test
  public void testCreateOf() {
    FixedSet<String> empty = FixedSet.of();
    assertTrue(empty.isEmpty());
    FixedSet<Integer> set1 = FixedSet.of(3);
    assertTrue(set1.size() == 1);
    assertTrue(set1.contains(3));
    assertFalse(set1.contains(4));
    FixedSet<String> set2 = FixedSet.of("ding", "dong");
    assertTrue(set2.size() == 2);
    assertTrue(set2.contains("ding"));
    assertTrue(set2.contains("dong"));
    FixedSet<Integer> fset = FixedSet.<Integer>of(-11, 9, 37, 12);
    assertTrue(fset.size() == 4);
    assertFalse(fset.isEmpty());
    assertTrue(fset.contains(-11));
    assertTrue(fset.contains(9));
    assertTrue(fset.contains(37));
    assertTrue(fset.contains(12));
  }

  @Test
  public void testCreateBuilder() {
    FixedSet.Builder<String> builderzero = FixedSet.<String>treeBuilder();
    assertTrue(builderzero.build().isEmpty());
    FixedSet.Builder<String> builder = FixedSet.<String>hashBuilder(2);
    builder.add("ape");
    builder.add("nut");
    FixedSet<String> fset = builder.build();
    assertThrows(java.lang.RuntimeException.class, () -> builder.add("test"));
    assertFalse(fset.isEmpty());
    assertTrue(fset.size() == 2);
    assertTrue(fset.contains("ape"));
    assertTrue(fset.contains("nut"));
  }

  @Test
  public void testStream() {
    TreeSet<String> tset = new TreeSet<String>();
    tset.add("Hello");
    tset.add("There");
    tset.add("Cruel");
    tset.add("World!");
    FixedSet<String> fset = FixedSet.<String>copy(tset);
    List<String> lst1 = fset.stream().toList();
    List<String> lst2 = fset.parallelStream().toList();
    assertTrue(lst1.equals(lst2));
    assertTrue(lst1.size() == 4);
    assertTrue(lst1.get(0).equals("Cruel"));
    assertTrue(lst1.get(1).equals("Hello"));
    assertTrue(lst1.get(2).equals("There"));
    assertTrue(lst1.get(3).equals("World!"));
  }

  @Test
  public void testIterate() {
    FixedSet<Integer> fset = FixedSet.<Integer>of(-11, 9, 37, 12);
    TreeSet<Integer> tmp = new TreeSet<Integer>();
    for (int x : fset) tmp.add(x);
    assertTrue(fset.equals(tmp));
  }

  @Test
  public void testCreateCopyWithNull() {
    TreeSet<String> empty = null;
    assertThrows(NullStorageException.class, () -> FixedSet.<String>copy(empty));
    HashSet<String> tset = new HashSet<String>();
    tset.add(null);
    tset.add("There");
    tset.add("World");
    assertThrows(NullStorageException.class, () -> FixedSet.<String>copy(tset));
    tset.remove(null);
    FixedSet.<String>copy(tset); // no more exception
  }

  @Test
  public void testOfWithNull() {
    assertThrows(NullStorageException.class, () -> FixedSet.of((Integer)null));
    assertThrows(NullStorageException.class, () -> FixedSet.of(null, "bing"));
    assertThrows(NullStorageException.class, () -> FixedSet.of("bing", null));
    assertThrows(NullStorageException.class, () -> FixedSet.of("bing", "bong", null));
    assertThrows(NullStorageException.class, () -> FixedSet.of(null, "bing", "bong"));
  }

  @Test
  public void testNullInBuilder() {
    FixedSet.Builder<String> builderzero = FixedSet.<String>hashBuilder(1);
    assertTrue(builderzero.build().isEmpty());
    FixedSet.Builder<String> builder = FixedSet.<String>treeBuilder();
    builder.add("ape");
    assertThrows(NullStorageException.class, () -> builder.add(null));
    builder.add("nut");
    FixedSet<String> fset = builder.build();
    assertTrue(fset.size() == 2);
    assertTrue(fset.contains("ape"));
    assertTrue(fset.contains("nut"));
  }
}

