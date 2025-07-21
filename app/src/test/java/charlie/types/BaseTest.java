/**************************************************************************************************
 Copyright 2019--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.types;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.util.NullStorageException;

class BaseTest {
  private Base intType() {
    return new Base("Int");
  }

  private Base boolType() {
    return new Base("Bool");
  }

  @Test
  void testConstructionWithNullGivesException() {
    assertThrows(NullStorageException.class,
      () -> new Base(null)
    );
  }

  @Test
  void testBasics() {
    Type t = intType();
    assertTrue(t.isBaseType());
    assertFalse(t.isArrowType());
    assertFalse(t.isProductType());
    assertTrue(t.equals(t));
    assertTrue(t.equals(intType()));
    assertFalse(t.equals(boolType()));
    assertTrue(t.queryArity() == 0);
    assertFalse(t.hasProducts());
  }

  @Test
  void testToStringIsJustTheName(){
    String name = java.util.UUID.randomUUID().toString();

    Type ty = new Base(name);
    assertEquals(name, ty.toString());
  }

  @Test
  void testTheoryType(){
    assertTrue(UniqueTypes.isTheoryType(TypeFactory.intSort));
    assertTrue(TypeFactory.boolSort.isTheoryType());
    assertTrue(TypeFactory.stringSort.isTheoryType());
    assertFalse(TypeFactory.defaultSort.isTheoryType());
    // despite the name, Int is only a theory type if it was created as such!
    assertFalse(intType().isTheoryType());
  }

  @Test
  void testTypeOrder() {
    assertEquals(0, (new Base("b")).queryTypeOrder());
  }

  @Test
  public void testHashCode() {
    Base a = new Base("A");
    Base b = new Base("A");
    assertTrue(a.hashCode() == b.hashCode());
  }
}

