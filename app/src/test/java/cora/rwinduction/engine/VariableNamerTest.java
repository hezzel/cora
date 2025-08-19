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

import java.util.ArrayList;
import java.util.TreeSet;

import charlie.util.Pair;
import charlie.types.TypeFactory;
import charlie.reader.CoraInputReader;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.FunctionSymbol;
import charlie.terms.TermFactory;
import charlie.trs.TRS;
import charlie.trs.TrsFactory;
import charlie.reader.CoraInputReader;

class VariableNamerTest {
  private VariableNamer createNamer() {
    return new VariableNamer(new ArrayList<Pair<Pair<FunctionSymbol,Integer>,String>>());
  }

  @Test
  public void testVariableInfo() {
    VariableNamer namer = createNamer();
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
    MutableRenaming renaming = new MutableRenaming(new TreeSet<String>());
    renaming.setName(x, "x");
    renaming.setName(y, "x1");
    renaming.setName(z, "x2");
    renaming.setName(u, "x4");
    renaming.setName(TermFactory.createVar("x"), "y3");
    VariableNamer namer = createNamer();
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

  @Test
  public void testSuitableVariablesForDerivative() {
    TRS trs = CoraInputReader.readTrsFromString("", TrsFactory.LCTRS);
    Term t = CoraInputReader.readTerm("(x ∧ y ≥ z) ∨ a", trs);
    VariableNamer namer = createNamer();
    TreeSet<Variable> set = namer.getSuitableVariablesForDerivative(t);
    assertTrue(set.size() == 2);
    assertTrue(set.first().queryName().equals("x"));
    assertTrue(set.last().queryName().equals("a"));
  }

  @Test
  public void testDerivativeNamingForTerm() {
    VariableNamer namer = createNamer();
    TRS trs = CoraInputReader.readTrsFromString("", TrsFactory.LCTRS);
    MutableRenaming renaming = new MutableRenaming(new TreeSet<String>());
    Term t;
    VariableNamer.VariableInfo info;

    // there is only one, and it has the right type
    renaming.setName(TermFactory.createVar("x", TypeFactory.intSort), "x12");
    t = CoraInputReader.readTerm("x12 + 17", renaming, trs);
    info = namer.chooseDerivativeNamingForTerm(t, renaming, "test");
    assertTrue(info.basename().equals("x"));
    assertTrue(info.index() == 13);

    // there are multiple, but only one has the right type
    renaming.setName(TermFactory.createVar("y3", TypeFactory.boolSort), "y3");
    t = CoraInputReader.readTerm("x12 > 17 ∧ y3", renaming, trs);
    info = namer.chooseDerivativeNamingForTerm(t, renaming, "test");
    assertTrue(info.basename().equals("y"));
    assertTrue(info.index() == 4);

    // there are none of the right type (yet multiple of the wrong type)
    renaming = new MutableRenaming(new TreeSet<String>());
    t = CoraInputReader.readTermAndUpdateNaming("x3 < y18", renaming, trs);
    info = namer.chooseDerivativeNamingForTerm(t, renaming, "test");
    assertTrue(info.basename().equals("test"));
    assertTrue(info.index() == 1);

    // there are multiple of the right type, with the same base name: x3 + x7 - x5
    t = CoraInputReader.readTermAndUpdateNaming("x3 * 5 + x18 - x5", renaming, trs);
    info = namer.chooseDerivativeNamingForTerm(t, renaming, "test");
    assertTrue(info.basename().equals("x"));
    assertTrue(info.index() == 19);

    // there are multiple of the right type, but with at least one having a different base name
    t = CoraInputReader.readTermAndUpdateNaming("x3 + x18 - y4 * 7", renaming, trs);
    info = namer.chooseDerivativeNamingForTerm(t, renaming, "test");
    assertTrue(info.basename().equals("test"));
    assertTrue(info.index() == 1);

    // there are multiple of the right type, but one has the default name
    t = CoraInputReader.readTermAndUpdateNaming("x3 + test12 - y4 * 7", renaming, trs);
    info = namer.chooseDerivativeNamingForTerm(t, renaming, "test");
    assertTrue(info.basename().equals("test"));
    assertTrue(info.index() == 13);
  }

  private void addTo(ArrayList<Pair<Pair<FunctionSymbol,Integer>,String>> info,
                                                        FunctionSymbol f, int index, String name) {
    Pair<FunctionSymbol,Integer> key = new Pair<FunctionSymbol,Integer>(f, index);
    info.add(new Pair<Pair<FunctionSymbol,Integer>,String>(key, name));
  }

  private Pair<FunctionSymbol,Integer> makepair(FunctionSymbol f, int index) {
    return new Pair<FunctionSymbol,Integer>(f, index);
  }

  @Test
  public void testDefaultNaming() {
    ArrayList<Pair<Pair<FunctionSymbol,Integer>,String>> info =
      new ArrayList<Pair<Pair<FunctionSymbol,Integer>,String>>();
    FunctionSymbol f = TermFactory.createConstant("f", CoraInputReader.readType("Int -> Int -> A"));
    FunctionSymbol g = TermFactory.createConstant("g", CoraInputReader.readType("Bool -> Int"));
    FunctionSymbol h = TermFactory.createConstant("h", CoraInputReader.readType("A -> A -> Bool"));
    addTo(info, f, 1, "x");
    addTo(info, f, 2, "y1");
    addTo(info, g, 1, "718");
    addTo(info, h, 1, "x3");
    addTo(info, h, 2, "z");
    addTo(info, f, 1, "x");
    addTo(info, f, 2, "y12");
    addTo(info, h, 1, "y3");
    addTo(info, h, 2, "z__");
    addTo(info, f, 2, "y10");
    VariableNamer namer = new VariableNamer(info);
    assertTrue(namer.queryDefaultNaming(f, 1).equals("x"));
    assertTrue(namer.queryDefaultNaming(f, 2).equals("y"));
    assertTrue(namer.queryDefaultNaming(g, 1) == null);
    assertTrue(namer.queryDefaultNaming(h, 1) == null);
    assertTrue(namer.queryDefaultNaming(h, 2) == null);
  }
}

