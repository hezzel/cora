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

package charlie.terms;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import charlie.types.Type;
import charlie.types.TypeFactory;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.ReplaceableList;

public class MetaVariableEnvironmentTest {
  private Type baseType(String name) {
    return TypeFactory.createSort(name);
  }
  
  private Type arrowType(String l, String r) {
    return TypeFactory.createArrow(baseType(l), baseType(r));
  }
  
  @Test
  public void testEnvironmentWithJustBinders() {
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Binder("x", baseType("a"));
    Replaceable z = new Binder("z", arrowType("a", "b"));
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(z);
    MetaVariableEnvironment env = new MetaVariableEnvironment(new ReplaceableList(set));
    assertTrue(env.size() == 0);
    for (MetaVariable v : env) { assertTrue(false); }
  }

  @Test
  public void testEnvironmentWithJustVariables() {
    Variable x = new Binder("x", baseType("a"));
    Var y = new Var("x", baseType("a"));
    Var z = new Var("z", arrowType("a", "b"));
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(z);
    MetaVariableEnvironment env = new MetaVariableEnvironment(new ReplaceableList(set));
    assertFalse(env.contains(y));
    assertTrue(env.contains(z));
    assertTrue(env.size() == 1);
    ArrayList<MetaVariable> parts = new ArrayList<MetaVariable>();
    for (MetaVariable v : env) parts.add(v);
    assertTrue(parts.get(0) == z);
  }

  @Test
  public void testEnvironmentWithJustMetavariables() {
    MetaVariable x = TermFactory.createMetaVar("x", arrowType("a", "a"), 1);
    MetaVariable y = TermFactory.createMetaVar("x", arrowType("a", "a"), 1);
    MetaVariable z = TermFactory.createMetaVar("x", arrowType("a", "a"), 1);
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(y);
    set.add(z);
    MetaVariableEnvironment env = new MetaVariableEnvironment(new ReplaceableList(set));
    assertTrue(env.size() == 3);
    ArrayList<MetaVariable> parts = new ArrayList<MetaVariable>();
    for (MetaVariable v : env) parts.add(v);
    assertTrue(parts.get(0) == x);
    assertTrue(parts.get(1) == y);
    assertTrue(parts.get(2) == z);
  }

  @Test
  public void testEnvironmentWithAllKinds() {
    Replaceable x = new Binder("x", baseType("a"));
    Replaceable y = new Var("y", baseType("b"));
    Replaceable z = TermFactory.createMetaVar("z", arrowType("a", "b"), 1);
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(y);
    set.add(z);
    MetaVariableEnvironment env = new MetaVariableEnvironment(new ReplaceableList(set));
    assertTrue(env.size() == 2);
    ArrayList<MetaVariable> parts = new ArrayList<MetaVariable>();
    for (MetaVariable v : env) parts.add(v);
    assertTrue(parts.get(0) == z);
    assertTrue(parts.get(1) == y);
  }
}

