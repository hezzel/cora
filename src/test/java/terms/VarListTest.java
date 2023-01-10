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

public class VarListTest {
  @Test
  public void testCreationWithThreeSimilarVariables() {
    Variable x = new Var("x", TypeFactory.createSort("a"), false);
    Var y = new Var("x", TypeFactory.createSort("a"), true);
    ArrayList<Variable> vars = new ArrayList<Variable>();
    vars.add(x);
    vars.add(y);
    vars.add(x);
    VarList lst = new VarList(vars);
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.size() == 2);
    vars.add(TermFactory.createVar("z"));
    assertTrue(lst.size() == 2);
  }

  @Test
  public void testInternalCreation() {
    TreeSet<Variable> set = new TreeSet<Variable>();
    Var x = new Var("x", TypeFactory.createSort("a"), false);
    Var y = new Var("y", TypeFactory.createSort("b"), true);
    set.add(x);
    set.add(y);
    VarList lst = new VarList(set, true);
    assertTrue(lst.contains(x));
    assertTrue(lst.contains(y));
    assertTrue(lst.size() == 2);
    Var z = new Var("z", TypeFactory.createSort("c"), false);
    set.add(z);
    assertTrue(lst.size() == 3);
    assertTrue(lst.contains(z));
  }

  @Test
  public void testRenaming() {
    Type a = TypeFactory.createSort("a");
    Type b = TypeFactory.createSort("b");
    Type ab = TypeFactory.createArrow(a, b);
    TreeSet<Variable> set = new TreeSet<Variable>();
    Variable x1 = new Var("x", a, false); set.add(x1);
    Variable x2 = new Var("x", a, false); set.add(x2);
    Variable x3 = new Var("x", b, true); set.add(x3);
    Variable y = new Var("y", b, true); set.add(y);
    Variable z1 = new Var("z", ab, true); set.add(z1);
    Variable z2 = new Var("z", ab, false); set.add(z2);
    VarList lst = new VarList(set);
    TreeMap<Variable,String> naming = lst.getUniqueNaming();
    assertTrue(naming.get(x1).equals("x__1"));
    assertTrue(naming.get(x2).equals("x__2"));
    assertTrue(naming.get(x3).equals("x__3"));
    assertTrue(naming.get(y).equals("y"));
    assertTrue(naming.get(z1).equals("z__1"));
    assertTrue(naming.get(z2).equals("z__2"));
  }
}

