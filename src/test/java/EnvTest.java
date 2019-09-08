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

public class EnvTest {
  @Test
  public void testAddContains() {
    Variable x = new Var("x", new Sort("a"));
    Var y = new Var("y", new Sort("b"));
    Var yy = new Var("y", new Sort("b"));
    Var z = new Var("z", new Sort("b"));
    Environment env = new Env();
    env.add(x);
    env.add(y);
    assertTrue(env.contains(x));
    assertTrue(env.contains(y));
    assertFalse(env.contains(yy));
    assertFalse(env.contains(z));
  }

  @Test
  public void testNameLookup() {
    Variable x = new Var("x", new Sort("a"));
    Var y = new Var("y", new Sort("b"));
    ArrayList<Variable> vars = new ArrayList<Variable>();
    vars.add(x);
    vars.add(y);
    Env env = new Env(vars);
    assertTrue(env.lookupName("x").equals(x));
    assertTrue(env.lookupName("y").equals(y));
    assertTrue(env.lookupName("z") == null);
  }

  @Test
  public void testAddVariableTwice() {
    Variable x = new Var("x", new Sort("a"));
    Environment env = new Env();
    env.add(x);
    env.add(x);
    assertTrue(env.contains(x));
  }

  @Test(expected = java.lang.Error.class)
  public void testAddingTwoVariablesWithTheSameName() {
    Variable x = new Var("x", new Sort("a"));
    Var y = new Var("x", new Sort("b"));
    Environment env = new Env();
    env.add(x);
    env.add(y);
  }

  @Test(expected = java.lang.Error.class)
  public void testCreationWithTwoVariablesWithTheSameName() {
    Variable x = new Var("x", new Sort("a"));
    Var y = new Var("x", new Sort("b"));
    ArrayList<Variable> vars = new ArrayList<Variable>();
    vars.add(x);
    vars.add(y);
    Env env = new Env(vars);
  }

  @Test
  public void testCopyingComplete() {
    Variable x = new Var("x", new Sort("a"));
    Variable y = new Var("y", new Sort("b"));
    Variable z = new Var("z", new Sort("c"));
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
}
