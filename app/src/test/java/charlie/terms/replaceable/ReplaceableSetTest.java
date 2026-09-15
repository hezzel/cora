/**************************************************************************************************
 Copyright 2023--2026 Cynthia Kop

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

import java.util.ArrayList;
import java.util.TreeSet;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.types.Type;
import charlie.types.TypeFactory;

public class ReplaceableSetTest {
  private Replaceable makeVar(String name, Type type) {
    return new MyReplaceable(name, type, 0);
  }

  private Replaceable makeMetaVar(String name) {
    return new MyReplaceable(name, TypeFactory.createSort("a"), 1);
  }

  @Test
  public void testCreationWithThreeSimilarVariables() {
    Replaceable x = makeVar("x", TypeFactory.createSort("a"));
    Replaceable y = makeVar("x", TypeFactory.createSort("a"));
    ArrayList<Replaceable> vars = new ArrayList<Replaceable>();
    vars.add(x);
    vars.add(y);
    vars.add(x);
    ReplaceableSet lst = new ReplaceableSet(vars);
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.size() == 2);
    vars.add(makeVar("z", TypeFactory.defaultSort));
    assertTrue(lst.size() == 2);
  }

  @Test
  public void testSingleCreation() {
    Replaceable x = makeMetaVar("x");
    ReplaceableSet lst = new ReplaceableSet(x);
    assertTrue(lst.contains(x));
    assertTrue(lst.size() == 1);
  }

  @Test
  public void testAdd() {
    Replaceable x = makeVar("x", TypeFactory.createSort("a"));
    Replaceable y = makeMetaVar("y");
    Replaceable z = makeVar("z", TypeFactory.createSort("a"));
    ReplaceableSet lst1 = new ReplaceableSet(x);
    ReplaceableSet lst2 = lst1.add(y);
    ReplaceableSet lst3 = lst2.add(z);
    assertTrue(lst1.size() == 1);
    assertTrue(lst2.size() == 2);
    assertTrue(lst3.size() == 3);
    assertTrue(lst2.contains(y));
    assertFalse(lst2.contains(z));
  }

  @Test
  public void testRemove() {
    Replaceable x = makeVar("x", TypeFactory.createSort("a"));
    Replaceable y = makeVar("y", TypeFactory.createSort("a"));
    Replaceable z = makeVar("z", TypeFactory.createSort("a"));
    ArrayList<Replaceable> vars = new ArrayList<Replaceable>();
    vars.add(x);
    vars.add(y);
    vars.add(z);
    ReplaceableSet lst3 = new ReplaceableSet(vars);
    ReplaceableSet lst2 = lst3.remove(x);
    ReplaceableSet lst1 = lst2.remove(z);
    assertTrue(lst1.size() == 1);
    assertTrue(lst2.size() == 2);
    assertTrue(lst3.size() == 3);
    assertTrue(lst3.contains(y));
    assertFalse(lst2.contains(x));
  }

  @Test
  public void testCombineEquals() {
    Replaceable x = makeVar("x", TypeFactory.createSort("a"));
    Replaceable y = makeVar("y", TypeFactory.createSort("a"));
    Replaceable z = makeMetaVar("z");
    ArrayList<Replaceable> reps = new ArrayList<Replaceable>();
    reps.add(x);
    reps.add(y);
    ReplaceableSet a = new ReplaceableSet(reps);
    reps.add(z);
    ReplaceableSet b = new ReplaceableSet(reps);
    assertTrue(a.combine(b) == b);
    assertTrue(b.combine(a) == b);
  }

  @Test
  public void testTrueCombination() {
    Replaceable x = makeMetaVar("x");
    Replaceable y = makeVar("y", TypeFactory.createSort("a"));
    Replaceable z = makeVar("z", TypeFactory.createSort("a"));
    ArrayList<Replaceable> reps = new ArrayList<Replaceable>();
    reps.add(x);
    reps.add(y);
    ReplaceableSet a = new ReplaceableSet(reps);
    reps.set(1, z);
    ReplaceableSet b = new ReplaceableSet(reps);
    ReplaceableSet c = a.combine(b);
    assertTrue(a.size() == 2);
    assertTrue(b.size() == 2);
    assertTrue(c.size() == 3);
    assertTrue(c.contains(x));
    assertTrue(c.contains(y));
    assertTrue(c.contains(z));
   }

   @Test
   public void testOverlap() {
    Replaceable x = makeVar("x", TypeFactory.createSort("a"));
    Replaceable y = makeMetaVar("y");
    Replaceable z = makeVar("x", TypeFactory.createSort("a"));
    Replaceable u = makeVar("u", TypeFactory.createSort("b"));
    ArrayList<Replaceable> reps1 = new ArrayList<Replaceable>();
    reps1.add(x);
    reps1.add(y);
    reps1.add(u);
    ReplaceableSet l1 = new ReplaceableSet(reps1);
    ArrayList<Replaceable> reps2 = new ArrayList<Replaceable>();
    reps2.add(z);
    reps2.add(y);
    reps2.add(u);
    ReplaceableSet l2 = new ReplaceableSet(reps2);

    TreeSet<Replaceable> overlap = l1.getOverlap(l2);
    assertTrue(overlap.size() == 2);
    assertTrue(overlap.contains(y));
    assertTrue(overlap.contains(u));
  }
}
