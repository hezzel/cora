/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.types;

import org.junit.Test;
import static org.junit.Assert.*;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import java.util.ArrayList;

public class SortTest {
  private BaseType intType() {
    return new Sort("Int", true);
  }

  private BaseType boolType() {
    return new Sort("Bool", false);
  }

  @Test(expected = NullInitialisationError.class)
  public void testConstructionWithNullGivesError() {
    Type x = new Sort(null, false);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testAskedForInputTypeError() {
    intType().queryArrowInputType();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testAskedForOutputTypeError() {
    boolType().queryArrowOutputType();
  }

  @Test
  public void testToStringIsJustTheName() {
    Type xxx = new Sort("x⇒X(x)~ ", true);
    assertTrue(xxx.toString().equals("x⇒X(x)~ "));
  }

  @Test
  public void testTheory() {
    assertTrue(intType().isTheorySort());
    assertTrue(intType().isTheoryType());
    Sort xx = new Sort("Int", false);
    assertFalse(xx.isTheorySort());
    assertFalse(xx.isTheoryType());
  }

  @Test
  public void testEqualityIsStringEquality() {
    ArrayList<Type> types;

    assertTrue(intType().equals(intType()));
    assertFalse(intType().equals(boolType()));
  }

  @Test
  public void testEqualityWithCapitals() {
    Type xxa = new Sort("xXx", true);
    Type xxb = new Sort("xXx", false);
    Type xxc = new Sort("xxX", false);
    assertTrue(xxa.equals(xxb));
    assertFalse(xxa.equals(xxc));
  }

  @Test
  public void testOutputSortIsItself() {
    assertTrue(intType().equals(intType().queryOutputSort()));
  }

  @Test
  public void testTypeKindIsBase() {
    assertTrue(intType().isBaseType());
    assertFalse(intType().isArrowType());
  }

  @Test
  public void testBaseTypeHasNoInputTypes() {
    Type inttype = intType();
    assertEquals(inttype.queryArity(), 0);
    ArrayList<Type> lst = new ArrayList<Type>();
    inttype.appendInputTypes(lst);
    assertTrue(lst.isEmpty());
  }

  @Test
  public void testTypeOrder() {
    assertEquals(0, intType().queryTypeOrder());
  }
}
