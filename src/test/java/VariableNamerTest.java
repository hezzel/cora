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
import cora.interfaces.rewriting.Alphabet;
import cora.types.Sort;
import cora.terms.Constant;
import cora.terms.UnitVariable;
import cora.terms.DefaultVariableNamer;
import cora.rewriting.UserDefinedAlphabet;

public class VariableNamerTest {
  @Test
  public void testNewVariableIsAssignedItsOwnName() {
    VariableNamer namer = new DefaultVariableNamer();
    Variable y = new UnitVariable("y");
    assertTrue(namer.assignName(y).equals("y"));
    assertTrue(namer.queryAssignedName(y).equals("y"));
  }

  @Test
  public void testSecondVariableWithTheSameNameIsChanged() {
    VariableNamer namer = new DefaultVariableNamer();
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
    
    VariableNamer namer = new DefaultVariableNamer(sigma);

    Variable z = new UnitVariable("x");
    String renamed = namer.assignName(z);
    assertFalse(renamed.equals("x"));
    assertFalse(renamed.equals("y"));
  }

  @Test
  public void testEntirelyNewName() {
    VariableNamer namer = new DefaultVariableNamer();
    Variable x = new UnitVariable();
    String name = namer.assignName(x);
    assertTrue(name != null);
  }
}
