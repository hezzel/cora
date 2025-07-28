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

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.types.Type;
import charlie.types.TypeFactory;

public class VariableEnvironmentTest {
  private Type baseType(String name) {
    return TypeFactory.createSort(name);
  }
  
  private Type arrowType(String l, String r) {
    return TypeFactory.createArrow(baseType(l), baseType(r));
  }
  
  @Test
  public void testEnvironmentWithJustVariables() {
    Variable x = new Binder("x", baseType("a"));
    Variable y = new Var("x", baseType("a"));
    Variable z = new Var("z", arrowType("a", "b"));
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(z);
    VariableEnvironment env = new VariableEnvironment(new ReplaceableList(set));
    assertTrue(env.contains(x));
    assertFalse(env.contains(y));
    assertTrue(env.contains(z));
    assertTrue(env.size() == 2);
    ArrayList<Variable> parts = new ArrayList<Variable>();
    for (Variable v : env) parts.add(v);
    assertTrue(parts.get(0) == z);
    assertTrue(parts.get(1) == x);
  }

  @Test
  public void testEnvironmentWithJustMetavariables() {
    MetaVariable x = TermFactory.createMetaVar("x", arrowType("a", "a"), 1);
    MetaVariable y = TermFactory.createMetaVar("x", arrowType("a", "a"), 1);
    MetaVariable z = TermFactory.createMetaVar("x", arrowType("a", "a"), 1);
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(y);
    set.add(z);
    VariableEnvironment env = new VariableEnvironment(new ReplaceableList(set));
    assertTrue(env.size() == 0);
    for (Variable v : env) { assertTrue(false); }
  }

  @Test
  public void testEnvironmentWithBothMetaAndNot() {
    Replaceable x = new Binder("x", baseType("a"));
    Replaceable y = new Var("y", baseType("b"));
    Replaceable z = TermFactory.createMetaVar("z", arrowType("a", "b"), 1);
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(y);
    set.add(z);
    VariableEnvironment env = new VariableEnvironment(new ReplaceableList(set));
    assertTrue(env.size() == 2);
    ArrayList<Variable> parts = new ArrayList<Variable>();
    for (Variable v : env) parts.add(v);
    assertTrue(parts.get(0) == y);
    assertTrue(parts.get(1) == x);
  }
}

