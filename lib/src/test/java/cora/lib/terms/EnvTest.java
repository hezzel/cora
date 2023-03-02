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

package cora.lib.terms;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.lib.types.Type;
import cora.lib.types.TypeFactory;

public class EnvTest {
  @Test
  public void testAddContains() {
    Variable x = new Var("x", TypeFactory.createSort("a"), false);
    Var y = new Var("y", TypeFactory.createSort("b"), true);
    Var yy = new Var("y", TypeFactory.createSort("b"), true);
    Var z = new Var("z", TypeFactory.createSort("b"), false);
    Environment env = new Env();
    env.add(x);
    env.add(y);
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertFalse(env.contains(yy));
    assertFalse(env.contains(z));
  }

  @Test
  public void testAddVariableTwice() {
    Variable x = new Var("x", TypeFactory.createSort("a"), false);
    Environment env = new Env();
    env.add(x);
    env.add(x);
    assertTrue(env.contains(x));
    assertTrue(env.size() == 1);
  }

  @Test
  public void testAddingTwoVariablesWithTheSameName() {
    Variable x = new Var("x", TypeFactory.createSort("a"), true);
    Var y = new Var("x", TypeFactory.createSort("b"), true);
    Environment env = new Env();
    env.add(x);
    env.add(y);
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertTrue(env.size() == 2);
  }

  @Test
  public void testCreationWithThreeSimilarVariables() {
    Variable x = new Var("x", TypeFactory.createSort("a"), false);
    Var y = new Var("x", TypeFactory.createSort("a"), true);
    ArrayList<Variable> vars = new ArrayList<Variable>();
    vars.add(x);
    vars.add(y);
    vars.add(x);
    Env env = new Env(vars);
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertTrue(env.size() == 2);
  }

  @Test
  public void testCopyingComplete() {
    Variable x = new Var("x", TypeFactory.createSort("a"), false);
    Variable y = new Var("y", TypeFactory.createSort("b"), true);
    Variable z = new Var("z", TypeFactory.createSort("c"), true);
    Environment env = new Env();
    env.add(x);
    env.add(y);
    env.add(z);
    Environment other = env.copy();
    boolean foundX = false;
    boolean foundY = false;
    boolean foundZ = false;
    for (Variable v : other) {
      if (v.equals(x)) foundX = true;
      if (v.equals(y)) foundY = true;
      if (v.equals(z)) foundZ = true;
    }
    assertTrue(foundX);
    assertTrue(foundY);
    assertTrue(foundZ);
  }

  @Test
  public void testImmutableCopy() {
    Variable x = new Var("x", TypeFactory.createSort("a"), false);
    Variable y = new Var("y", TypeFactory.createSort("b"), true);
    Variable z = new Var("z", TypeFactory.createSort("c"), true);
    Environment env = new Env();
    env.add(x);
    env.add(y);
    env.add(z);
    VariableList lst = env.getImmutableCopy();
    boolean foundX = false;
    boolean foundY = false;
    boolean foundZ = false;
    for (Variable v : lst) {
      if (v.equals(x)) foundX = true;
      if (v.equals(y)) foundY = true;
      if (v.equals(z)) foundZ = true;
    }
    assertTrue(foundX);
    assertTrue(foundY);
    assertTrue(foundZ);
    assertTrue(lst.size() == env.size());
  }
}

