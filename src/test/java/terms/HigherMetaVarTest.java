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
import cora.exceptions.*;
import cora.types.Type;
import cora.types.TypeFactory;

public class HigherMetaVarTest {
  @Test(expected = NullInitialisationError.class)
  public void testCreateWithNullName() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(TypeFactory.createSort("a"));
    inputs.add(TypeFactory.createSort("b"));
    MetaVariable z = new HigherMetaVar(null, inputs, TypeFactory.createSort("c"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateWithNullInputs() {
    MetaVariable z = new HigherMetaVar("z", null, TypeFactory.createSort("c"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateWithSingleNullInput() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(TypeFactory.createSort("a"));
    inputs.add(TypeFactory.createSort(null));
    MetaVariable z = new HigherMetaVar("z", inputs, TypeFactory.createSort("c"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testCreateWithNullOutput() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(TypeFactory.createSort("a"));
    inputs.add(TypeFactory.createSort("b"));
    MetaVariable z = new HigherMetaVar("z", inputs, null);
  }

  @Test(expected = IllegalArgumentError.class)
  public void testCreateWithEmptyInputs() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    MetaVariable z = new HigherMetaVar("z", inputs, TypeFactory.createSort("c"));
  }

  @Test
  public void testCorrectCreation() {
    ArrayList<Type> inputs = new ArrayList<Type>();
    inputs.add(TypeFactory.createSort("a"));
    inputs.add(TypeFactory.createSort("b"));
    MetaVariable z = new HigherMetaVar("z", inputs, TypeFactory.createSort("c"));
    assertTrue(z.queryName().equals("z"));
    assertTrue(z.queryArity() == 2);
    assertTrue(z.queryInputType(1).equals(TypeFactory.createSort("a")));
    assertTrue(z.queryInputType(2).equals(TypeFactory.createSort("b")));
    assertTrue(z.queryOutputType().equals(TypeFactory.createSort("c")));
    assertTrue(z.queryType().toString().equals("a ⇒ b ⇒ c"));
    assertTrue(z.equals(z));
    MetaVariable z2 = new HigherMetaVar("z", inputs, TypeFactory.createSort("c"));
    assertFalse(z.equals(z2));
    assertTrue(z.toString().equals("z"));
  }

  @Test
  public void testFactoryCreation() {
    Type type = TypeFactory.createArrow(TypeFactory.createSort("a"),
      TypeFactory.createArrow(TypeFactory.createSort("b"),
        TypeFactory.createArrow(TypeFactory.createSort("c"),
          TypeFactory.createArrow(TypeFactory.createSort("d"),
            TypeFactory.createSort("e")))));
    MetaVariable x = TermFactory.createMetaVar("xx", type, 3);
    assertTrue(x.queryName().equals("xx"));
    assertTrue(x.queryArity() == 3);
    assertTrue(x.queryInputType(1).equals(TypeFactory.createSort("a")));
    assertTrue(x.queryInputType(2).equals(TypeFactory.createSort("b")));
    assertTrue(x.queryInputType(3).equals(TypeFactory.createSort("c")));
    assertTrue(x.queryOutputType().toString().equals("d ⇒ e"));
    assertTrue(x.queryType().equals(type));
  }
}
