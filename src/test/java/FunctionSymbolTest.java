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
import java.lang.Error;
import java.util.ArrayList;
import cora.exceptions.NullInitialisationError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;
import cora.immutabledata.types.*;
import cora.immutabledata.terms.UserDefinedSymbol;

public class FunctionSymbolTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  @Test(expected = NullInitialisationError.class)
  public void testUserDefinedSymbolNullName() {
    FunctionSymbol f = new UserDefinedSymbol(null, baseType("o"));
  }

  @Test(expected = java.lang.Error.class)
  public void testUserDefinedSymbolEmptyName() {
    FunctionSymbol f = new UserDefinedSymbol("", baseType("o"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testUserDefinedSymbolNullType() {
    FunctionSymbol f = new UserDefinedSymbol("bing", null);
  }

  @Test
  public void testUserDefinedSymbolBasics() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    FunctionSymbol f = new UserDefinedSymbol("ff", combi);
    assertTrue(f.queryName().equals("ff"));
    assertTrue(f.toString().equals("ff"));
    assertTrue(f.queryType().equals(combi));
  }

  @Test
  public void testUserDefinedSymbolEquality() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    FunctionSymbol f = new UserDefinedSymbol("ff", combi);
    FunctionSymbol g = new UserDefinedSymbol("ff", combi);
    FunctionSymbol h = new UserDefinedSymbol("f", combi);
    FunctionSymbol i = new UserDefinedSymbol("f", new ArrowType(a,c));

    assertTrue(f.equals(g));
    assertFalse(f.equals(h));
    assertFalse(f.equals(i));
    assertFalse(f.equals(null));
  }
}
