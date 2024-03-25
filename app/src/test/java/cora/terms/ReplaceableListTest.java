/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;
import cora.types.Type;
import cora.types.TypeFactory;

public class ReplaceableListTest {
  private MetaVariable makeMetaVar(String name) {
    return TermFactory.createMetaVar(name,
      TypeFactory.createArrow(TypeFactory.createSort("a"), TypeFactory.createSort("a")), 1);
  }

  @Test
  public void testCreationWithThreeSimilarVariables() {
    Variable x = new Var("x", TypeFactory.createSort("a"));
    Variable y = new Binder("x", TypeFactory.createSort("a"));
    ArrayList<Replaceable> vars = new ArrayList<Replaceable>();
    vars.add(x);
    vars.add(y);
    vars.add(x);
    ReplaceableList lst = new ReplaceableList(vars);
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.size() == 2);
    vars.add(TermFactory.createVar("z"));
    assertTrue(lst.size() == 2);
  }

  @Test
  public void testSingleCreation() {
    MetaVariable x = makeMetaVar("x");
    ReplaceableList lst = new ReplaceableList(x);
    assertTrue(lst.contains(x));
    assertTrue(lst.size() == 1);
  }

  @Test
  public void testAdd() {
    Variable x = new Var("x", TypeFactory.createSort("a"));
    Replaceable y = makeMetaVar("y");
    Replaceable z = new Var("z", TypeFactory.createSort("a"));
    ReplaceableList lst1 = new ReplaceableList(x);
    ReplaceableList lst2 = lst1.add(y);
    ReplaceableList lst3 = lst2.add(z);
    assertTrue(lst1.size() == 1);
    assertTrue(lst2.size() == 2);
    assertTrue(lst3.size() == 3);
    assertTrue(lst2.contains(y));
    assertFalse(lst2.contains(z));
  }

  @Test
  public void testRemove() {
    Variable x = new Var("x", TypeFactory.createSort("a"));
    Variable y = new Var("y", TypeFactory.createSort("a"));
    Variable z = new Var("z", TypeFactory.createSort("a"));
    ArrayList<Replaceable> vars = new ArrayList<Replaceable>();
    vars.add(x);
    vars.add(y);
    vars.add(z);
    ReplaceableList lst3 = new ReplaceableList(vars);
    ReplaceableList lst2 = lst3.remove(x);
    ReplaceableList lst1 = lst2.remove(z);
    assertTrue(lst1.size() == 1);
    assertTrue(lst2.size() == 2);
    assertTrue(lst3.size() == 3);
    assertTrue(lst3.contains(y));
    assertFalse(lst2.contains(x));
  }

  @Test
  public void testCombineEquals() {
    Variable x = new Var("x", TypeFactory.createSort("a"));
    Variable y = new Var("y", TypeFactory.createSort("a"));
    Replaceable z = makeMetaVar("z");
    ArrayList<Replaceable> reps = new ArrayList<Replaceable>();
    reps.add(x);
    reps.add(y);
    ReplaceableList a = new ReplaceableList(reps);
    reps.add(z);
    ReplaceableList b = new ReplaceableList(reps);
    assertTrue(a.combine(b) == b);
    assertTrue(b.combine(a) == b);
  }

  @Test
  public void testTrueCombination() {
    Replaceable x = makeMetaVar("x");
    Replaceable y = new Var("y", TypeFactory.createSort("a"));
    Replaceable z = new Var("z", TypeFactory.createSort("a"));
    ArrayList<Replaceable> reps = new ArrayList<Replaceable>();
    reps.add(x);
    reps.add(y);
    ReplaceableList a = new ReplaceableList(reps);
    reps.set(1, z);
    ReplaceableList b = new ReplaceableList(reps);
    ReplaceableList c = a.combine(b);
    assertTrue(a.size() == 2);
    assertTrue(b.size() == 2);
    assertTrue(c.size() == 3);
    assertTrue(c.contains(x));
    assertTrue(c.contains(y));
    assertTrue(c.contains(z));
   }

   @Test
   public void testOverlap() {
    Replaceable x = new Var("x", TypeFactory.createSort("a"));
    Replaceable y = makeMetaVar("y");
    Replaceable z = new Var("x", TypeFactory.createSort("a"));
    Replaceable u = new Binder("u", TypeFactory.createSort("b"));
    ArrayList<Replaceable> reps1 = new ArrayList<Replaceable>();
    reps1.add(x);
    reps1.add(y);
    reps1.add(u);
    ReplaceableList l1 = new ReplaceableList(reps1);
    ArrayList<Replaceable> reps2 = new ArrayList<Replaceable>();
    reps2.add(z);
    reps2.add(y);
    reps2.add(u);
    ReplaceableList l2 = new ReplaceableList(reps2);

    TreeSet<Replaceable> overlap = l1.getOverlap(l2);
    assertTrue(overlap.size() == 2);
    assertTrue(overlap.contains(y));
    assertTrue(overlap.contains(u));
  }
}

