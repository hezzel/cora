/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

class FixedListTest {
  @Test
  public void testCreateCopy() {
    LinkedList<String> llst = new LinkedList<String>();
    llst.add("Hello");
    llst.add("there");
    llst.add("World");
    FixedList<String> flst = FixedList.<String>copy(llst);
    assertTrue(flst.size() == 3);
    assertTrue(flst.equals(llst));
    assertTrue(flst.hashCode() == llst.hashCode());
    assertTrue(flst.get(0).equals("Hello"));
    assertTrue(flst.get(1).equals("there"));
    assertTrue(flst.get(2).equals("World"));
    assertFalse(flst.isEmpty());
    assertTrue(flst.contains("there"));
    assertFalse(flst.contains("There"));
    llst.set(1, "There");
    assertTrue(flst.get(1).equals("there"));
    assertFalse(flst.contains("There"));
  }

  @Test
  public void testCreateOf() {
    FixedList<String> empty = FixedList.of();
    assertTrue(empty.isEmpty());
    FixedList<Integer> lst1 = FixedList.of(3);
    assertTrue(lst1.size() == 1);
    assertTrue(lst1.get(0).equals(3));
    FixedList<String> lst2 = FixedList.of("ding", "dong");
    assertTrue(lst2.size() == 2);
    assertTrue(lst2.get(0).equals("ding"));
    assertTrue(lst2.get(1).equals("dong"));
    FixedList<Integer> flst = FixedList.<Integer>of(-11, 9, 37, 12);
    assertTrue(flst.size() == 4);
    assertFalse(flst.isEmpty());
    assertTrue(flst.get(0) == -11);
    assertTrue(flst.get(1) == 9);
    assertTrue(flst.get(2) == 37);
    assertTrue(flst.get(3) == 12);
    assertThrows(java.lang.IndexOutOfBoundsException.class, () -> flst.get(4));
  }

  @Test
  public void testCreateBuilder() {
    FixedList.Builder<String> builderzero = new FixedList.Builder<String>();
    assertTrue(builderzero.build().isEmpty());
    FixedList.Builder<String> builder = new FixedList.Builder<String>();
    builder.add("ape");
    builder.add("nut");
    FixedList<String> flst = builder.build();
    assertThrows(java.lang.RuntimeException.class, () -> builder.add("test"));
    assertFalse(flst.isEmpty());
    assertTrue(flst.size() == 2);
    assertTrue(flst.get(0).equals("ape"));
    assertTrue(flst.get(1).equals("nut"));
  }

  @Test
  public void testStream() {
    LinkedList<String> llst = new LinkedList<String>();
    llst.add("Hello");
    llst.add("There");
    llst.add("Cruel");
    llst.add("World!");
    FixedList<String> flst = FixedList.<String>copy(llst);
    assertTrue(llst.equals(flst.stream().toList()));
    assertTrue(llst.equals(flst.parallelStream().toList()));
  }

  @Test
  public void testIterate() {
    FixedList<Integer> flst = FixedList.<Integer>of(-11, 9, 37, 12);
    ArrayList<Integer> tmp = new ArrayList<Integer>(4);
    for (int x : flst) tmp.add(x);
    assertTrue(flst.equals(tmp));
  }

  @Test
  public void testCreateCopyWithNull() {
    LinkedList<String> empty = null;
    assertThrows(NullStorageException.class, () -> FixedList.<String>copy(empty));
    LinkedList<String> llst = new LinkedList<String>();
    llst.add(null);
    llst.add("There");
    llst.add("World");
    assertThrows(NullStorageException.class, () -> FixedList.<String>copy(llst));
    llst.set(0, "Hello");
    llst.set(2, null);
    assertThrows(NullStorageException.class, () -> FixedList.<String>copy(llst));
    llst.set(2, "World");
    FixedList.<String>copy(llst); // no more exception
  }

  @Test
  public void testOfWithNull() {
    assertThrows(NullStorageException.class, () -> FixedList.of((Integer)null));
    assertThrows(NullStorageException.class, () -> FixedList.of(null, "bing"));
    assertThrows(NullStorageException.class, () -> FixedList.of("bing", null));
    assertThrows(NullStorageException.class, () -> FixedList.of("bing", "bong", null));
    assertThrows(NullStorageException.class, () -> FixedList.of(null, "bing", "bong"));
  }

  @Test
  public void testNullInBuilder() {
    FixedList.Builder<String> builderzero = new FixedList.Builder<String>();
    assertTrue(builderzero.build().isEmpty());
    FixedList.Builder<String> builder = new FixedList.Builder<String>();
    builder.add("ape");
    assertThrows(NullStorageException.class, () -> builder.add(null));
    builder.add("nut");
    FixedList<String> flst = builder.build();
    assertTrue(flst.size() == 2);
    assertTrue(flst.get(0).equals("ape"));
    assertTrue(flst.get(1).equals("nut"));
  }
}

