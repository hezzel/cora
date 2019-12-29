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
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.VariableNamer;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Alphabet;
import cora.types.Sort;
import cora.types.ArrowType;
import cora.terms.Constant;
import cora.terms.Var;
import cora.terms.UnitVariable;
import cora.terms.BinderVariable;
import cora.terms.CleverVariableNamer;
import cora.terms.Env;
import cora.terms.UserDefinedAlphabet;

public class VariableNamerTest {
  @Test
  public void testNewVariableIsAssignedItsOwnName() {
    VariableNamer namer = new CleverVariableNamer();
    Variable y = new UnitVariable("y");
    assertTrue(namer.assignName(y).equals("y"));
    assertTrue(namer.queryAssignedName(y).equals("y"));
  }

  @Test
  public void testSecondVariableWithTheSameNameIsChanged() {
    VariableNamer namer = new CleverVariableNamer();
    Variable x = new UnitVariable("y");
    Variable y = new UnitVariable("y");
    String name1 = namer.assignName(x);
    String name2 = namer.assignName(y);
    assertFalse(name1.equals(name2));
    assertTrue(namer.queryAssignedName(y).equals(name2));
    assertTrue(namer.queryAssignedName(x).equals(name1));
  }

  @Test
  public void testAvoidNameInAlphabet() {
    FunctionSymbol x = new Constant("x", Sort.unitSort);
    FunctionSymbol y = new Constant("y", new Sort("a"));
    ArrayList<FunctionSymbol> xy = new ArrayList<FunctionSymbol>();
    xy.add(x);
    xy.add(y);
    Alphabet sigma = new UserDefinedAlphabet(xy);
    
    VariableNamer namer = new CleverVariableNamer(sigma);

    Variable z = new UnitVariable("x");
    String renamed = namer.assignName(z);
    assertFalse(renamed.equals("x"));
    assertFalse(renamed.equals("y"));
  }


  @Test
  public void testPreAssignNames() {
    ArrayList<Variable> lst = new ArrayList<Variable>();
    Variable x = new UnitVariable("x");
    Variable y = new UnitVariable("x");
    Variable z = new UnitVariable("z");
    lst.add(x);
    lst.add(y);
    lst.add(z);
    Env env = new Env(lst);
    Alphabet sigma = new UserDefinedAlphabet(new ArrayList<FunctionSymbol>());
    VariableNamer namer = new CleverVariableNamer(sigma, env);
    assertTrue(namer.queryAssignedName(x).equals("x"));
    assertTrue(namer.queryAssignedName(y) == null);
    assertTrue(namer.queryAssignedName(z).equals("z"));
  }

  @Test
  public void testPreAssignNamesWithReversedDuplicates() {
    ArrayList<Variable> lst = new ArrayList<Variable>();
    Variable x = new UnitVariable("x");
    Variable y = new UnitVariable("x");
    Variable z = new UnitVariable("z");
    lst.add(y);
    lst.add(x);
    lst.add(z);
    Env env = new Env(lst);
    Alphabet sigma = new UserDefinedAlphabet(new ArrayList<FunctionSymbol>());
    VariableNamer namer = new CleverVariableNamer(sigma, env);
    assertTrue(namer.queryAssignedName(x).equals("x"));
    assertTrue(namer.queryAssignedName(y) == null);
    assertTrue(namer.queryAssignedName(z).equals("z"));
  }

  @Test
  public void testPreAssignNameWithAlphabetOverlap() {
    ArrayList<Variable> lst = new ArrayList<Variable>();
    Variable x = new UnitVariable("x");
    Variable y = new UnitVariable("x");
    Variable z = new UnitVariable("z");
    lst.add(x);
    lst.add(y);
    lst.add(z);
    Env env = new Env(lst);

    ArrayList<FunctionSymbol> alf = new ArrayList<FunctionSymbol>();
    alf.add(new Constant("c", Sort.unitSort));
    alf.add(new Constant("z", Sort.unitSort));
    Alphabet sigma = new UserDefinedAlphabet(alf);

    VariableNamer namer = new CleverVariableNamer(sigma, env);
    assertTrue(namer.queryAssignedName(x).equals("x"));
    assertTrue(namer.queryAssignedName(y) == null);
    assertTrue(namer.queryAssignedName(z) == null);
  }

  @Test
  public void testEntirelyNewName() {
    VariableNamer namer = new CleverVariableNamer();
    Variable x = new UnitVariable();
    String name = namer.assignName(x);
    assertTrue(name != null);
  }

  @Test
  public void testBoundAndFreeVariablesGetDifferentNames() {
    VariableNamer namer1 = new CleverVariableNamer();
    VariableNamer namer2 = new CleverVariableNamer();
    VariableNamer namer3 = new CleverVariableNamer();
    Variable x = new Var(new Sort("a"));
    Variable y = new UnitVariable();
    Variable z = new BinderVariable(new Sort("a"));
    String xname = namer1.assignName(x);
    String yname = namer2.assignName(y);
    String zname = namer3.assignName(z);
    assertTrue(xname.equals(yname));
    assertFalse(xname.equals(zname));
  }

  @Test
  public void testBaseAndHigherVariablesGetDifferentNames() {
    VariableNamer namer1 = new CleverVariableNamer();
    VariableNamer namer2 = new CleverVariableNamer();
    VariableNamer namer3 = new CleverVariableNamer();
    Variable x = new Var(new Sort("a"));
    Variable y = new Var(new ArrowType(new Sort("a"), new Sort("b")));
    Variable z = new Var(new ArrowType(new Sort("c"), new ArrowType(new Sort("a"), new Sort("b"))));
    String xname = namer1.assignName(x);
    String yname = namer2.assignName(y);
    String zname = namer3.assignName(z);
    assertFalse(xname.equals(yname));
    assertTrue(yname.equals(zname));
  }
}
