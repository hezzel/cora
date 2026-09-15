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
import java.util.TreeSet;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.types.Type;
import charlie.parser.CoraParser;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.ReplaceableSet;

public class VariableEnvironmentTest {
  private Type type(String desc) { return CoraParser.readType(desc); }

  @Test
  public void testEnvironmentWithJustVariables() {
    Variable x = new Binder("x", type("a"));
    Variable y = new Var("x", type("a"));
    Variable z = new Var("z", type("a -> b"));
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(z);
    VariableEnvironment env = new VariableEnvironment(new ReplaceableSet(set));
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
    MetaVariable x = TermFactory.createMetaVar("x", type("a -> a"), 1);
    MetaVariable y = TermFactory.createMetaVar("x", type("a -> a"), 1);
    MetaVariable z = TermFactory.createMetaVar("x", type("a -> a"), 1);
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(y);
    set.add(z);
    VariableEnvironment env = new VariableEnvironment(new ReplaceableSet(set));
    assertTrue(env.size() == 0);
    for (Variable v : env) { assertTrue(false); }
  }

  @Test
  public void testEnvironmentWithBothMetaAndNot() {
    Replaceable x = new Binder("x", type("a"));
    Replaceable y = new Var("y", type("b"));
    Replaceable z = TermFactory.createMetaVar("z", type("a -> b"), 1);
    TreeSet<Replaceable> set = new TreeSet<Replaceable>();
    set.add(x);
    set.add(y);
    set.add(z);
    VariableEnvironment env = new VariableEnvironment(new ReplaceableSet(set));
    assertTrue(env.size() == 2);
    ArrayList<Variable> parts = new ArrayList<Variable>();
    for (Variable v : env) parts.add(v);
    assertTrue(parts.get(0) == y);
    assertTrue(parts.get(1) == x);
  }
}
