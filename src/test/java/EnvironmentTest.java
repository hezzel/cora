/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Environment;
import cora.types.*;
import cora.terms.Var;
import cora.terms.Env;

public class EnvironmentTest {
  @Test
  public void testEmptyConstruction() {
    Env env = new Env();
    assertEquals(env.size(), 0);
  }

  @Test
  public void testSingleConstruction() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("x", new Sort("a"));
    Env env = new Env(x);
    assertEquals(env.size(), 1);
    assertTrue(env.contains(x));
    assertFalse(env.contains(y));
  }

  @Test
  public void testListConstruction() {
    ArrayList<Environment> lst = new ArrayList<Environment>();
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("x", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));
    Environment env1 = new Env(x);
    Environment env2 = new Env(y);
    lst.add(env1.extend(y));
    lst.add(env2.extend(z));
    Environment combi = new Env(lst);

    assertEquals(combi.size(), 3);
    assertTrue(combi.contains(x));
    assertTrue(combi.contains(y));
    assertTrue(combi.contains(z));
  }

  @Test
  public void testCollectionConstruction() {
    ArrayList<Variable> lst = new ArrayList<Variable>();
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("x", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));
    lst.add(x);
    lst.add(y);
    lst.add(x);

    Env env = new Env(lst);

    assertEquals(env.size(), 2);
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertFalse(env.contains(z));
  }

  @Test
  public void testContainsAll() {
    ArrayList<Variable> lst = new ArrayList<Variable>();
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("x", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));
    lst.add(x);
    lst.add(y);

    Env env1 = new Env(lst);
    lst.add(z);
    Env env2 = new Env(lst);

    assertTrue(env2.containsAll(env1));
    assertTrue(env2.containsAll(env2));
    assertFalse(env1.containsAll(env2));
  }

  @Test
  public void testIterator() {
    ArrayList<Variable> lst = new ArrayList<Variable>();
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("x", new Sort("a"));
    lst.add(x);
    lst.add(y);

    Env env = new Env(lst);
    boolean xdone = false;
    boolean ydone = false;

    for (Variable z : env) {
      if (z.equals(x)) xdone = true;
      if (z.equals(y)) ydone = true;
    }

    assertTrue(xdone);
    assertTrue(ydone);
  }

  @Test
  public void testExtend() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("x", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));

    Environment env = new Env(x);
    env = env.extend(z);
    env = env.extend(y);
    env = env.extend(y);

    assertTrue(env.size() == 3);
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertTrue(env.contains(z));
  }

  @Test
  public void testRemove() {
    ArrayList<Variable> lst = new ArrayList<Variable>();
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("x", new Sort("a"));
    Variable z = new Var("z", new Sort("a"));
    lst.add(x);
    lst.add(y);

    Environment env = new Env(lst);
    assertTrue(env.size() == 2);
    env = env.remove(z);
    assertTrue(env.size() == 2);
    env = env.remove(x);
    assertTrue(env.size() == 1);
    env = env.remove(x);
    assertTrue(env.size() == 1);
    env = env.remove(y);
    assertTrue(env.size() == 0);
    env = env.remove(y);
    assertTrue(env.size() == 0);
  }
}
