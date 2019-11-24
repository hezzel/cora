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
import java.util.TreeMap;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;

public class RenameTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private class TestVariableNamer implements VariableNamer {
    TreeMap<String,Variable> nameToVariable;
    TreeMap<Variable,String> variableToName;
    ArrayList<String> unused;
    int unusedIndex;

    public TestVariableNamer() {
      nameToVariable = new TreeMap<String,Variable>();
      variableToName = new TreeMap<Variable,String>();
      unused = new ArrayList<String>();
      unusedIndex = 0;
    }

    public void add(String name) {
      unused.add(name);
    }

    public String queryAssignedName(Variable x) {
      return variableToName.get(x);
    }

    public String assignName(Variable x) {
      if (variableToName.get(x) != null) return variableToName.get(x);
      if (unusedIndex >= unused.size()) throw new Error("Not enough variables in mock.");
      String name = unused.get(unusedIndex);
      unusedIndex++;
      nameToVariable.put(name, x);
      variableToName.put(x, name);
      return name;
    }
  }

  VariableNamer createNamer() {
    TestVariableNamer namer = new TestVariableNamer();
    namer.add("x");
    namer.add("y");
    namer.add("z");
    namer.add("v0");
    namer.add("v1");
    namer.add("v2");
    namer.add("v3");
    namer.add("v4");
    namer.add("v5");
    return namer;
  }

  @Test
  public void testLinearTerm() {
    Type a = new Sort("a");
    Type b = new Sort("b");
    Type c = new Sort("c");
    Type bc = new ArrowType(b, c);
    Type abc = new ArrowType(a, bc);

    Variable x = new Var(abc);
    Variable y = new Var(b);
    Variable z = new Var(abc);
    Variable u = new Var(a);
    // f(g(x(aa, bb), y), z(u))
    FunctionSymbol aa = new Constant("aa", a);
    FunctionSymbol bb = new Constant("bb", b);
    FunctionSymbol g = new Constant("g", new ArrowType(c, new ArrowType(b, a)));
    FunctionSymbol f = new Constant("f", new ArrowType(a, new ArrowType(bc, b)));
    Term xab = new VarTerm(x, aa, bb);
    Term zu = new VarTerm(z, u);
    Term gxaabby = new FunctionalTerm(g, xab, y);
    Term full = new FunctionalTerm(f, gxaabby, zu);

    // pretty-print it!
    VariableNamer namer = createNamer();
    assertTrue(full.toString(namer).equals("f(g(x(aa, bb), y), z(v0))"));
    assertTrue(namer.queryAssignedName(x).equals("x"));
    assertTrue(namer.queryAssignedName(y).equals("y"));
    assertTrue(namer.queryAssignedName(z).equals("z"));
    assertTrue(namer.queryAssignedName(u).equals("v0"));
  }

  @Test
  public void testNonLinearTerm() {
    Type a = new Sort("a");
    Type b = new Sort("b");
    Type c = new Sort("c");
    Type bc = new ArrowType(b, c);
    Type abc = new ArrowType(a, bc);

    Variable x = new Var(abc);
    Variable y = new Var(b);
    Variable z = new Var(bc);
    // f(g(x(aa, bb), y), z(y))
    FunctionSymbol aa = new Constant("aa", a);
    FunctionSymbol bb = new Constant("bb", b);
    FunctionSymbol g = new Constant("g", new ArrowType(c, new ArrowType(b, a)));
    FunctionSymbol f = new Constant("f", new ArrowType(a, new ArrowType(c, b)));
    Term xab = new VarTerm(x, aa, bb);
    Term zy = new VarTerm(z, y);
    Term gxaabby = new FunctionalTerm(g, xab, y);
    Term full = new FunctionalTerm(f, gxaabby, zy);

    // pretty-print it!
    VariableNamer namer = createNamer();
    assertTrue(full.toString(namer).equals("f(g(x(aa, bb), y), z(y))"));
  }
}

