/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;

import charlie.types.TypeFactory;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.terms.TermFactory;

class VariableNamerTest {
  @Test
  public void testVariableInfo() {
    VariableNamer namer = new VariableNamer();
    VariableNamer.VariableInfo info;

    info = namer.getVariableInfo("x", "x13");
    assertTrue(info.basename().equals("x"));
    assertTrue(info.index() == 13);

    info = namer.getVariableInfo("x", "x_134780");
    assertTrue(info.basename().equals("x"));
    assertTrue(info.index() == 134780);

    info = namer.getVariableInfo("x", "y_42");
    assertTrue(info.basename().equals("y_"));
    assertTrue(info.index() == 42);

    info = namer.getVariableInfo("x", "z");
    assertTrue(info.basename().equals("z"));
    assertTrue(info.index() == 0);

    info = namer.getVariableInfo("q", "x-3");
    assertTrue(info.basename().equals("x-"));
    assertTrue(info.index() == 3);
  }

  @Test
  public void testChooseDerivativeNaming() {
    Variable x = TermFactory.createVar("x");
    Variable y = TermFactory.createVar("x1");
    Variable z = TermFactory.createVar("x");
    Variable u = TermFactory.createVar("x");
    Renaming renaming = new Renaming(Set.of());
    renaming.setName(x, "x");
    renaming.setName(y, "x1");
    renaming.setName(z, "x2");
    renaming.setName(u, "x4");
    renaming.setName(TermFactory.createVar("x"), "y3");
    VariableNamer namer = new VariableNamer();
    VariableNamer.VariableInfo info = namer.chooseDerivativeNaming(x, renaming);
    assertTrue(info.basename().equals("x"));
    assertTrue(info.index() == 3);
    Variable v = namer.chooseDerivative(y, renaming, TypeFactory.intSort);
    assertTrue(v.queryName().equals("x"));
    assertTrue(renaming.getName(v).equals("x3"));
    v = namer.chooseDerivative(v, renaming, TypeFactory.defaultSort);
    assertTrue(v.queryName().equals("x"));
    assertTrue(renaming.getName(v).equals("x5"));
  }
}

