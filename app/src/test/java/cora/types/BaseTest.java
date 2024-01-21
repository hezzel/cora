/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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

import cora.exceptions.NullInitialisationError;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;

import static org.junit.jupiter.api.Assertions.*;

class BaseTest {
  @Contract(" -> new")
  private @NotNull Base intType() {
    return new Base("Int");
  }

  @Contract(" -> new")
  private @NotNull Base boolType() {
    return new Base("Bool");
  }

  @Test
  void testConstructionWithNullGivesError(){
    Assertions.assertThrows(NullInitialisationError.class,
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
    assertFalse(TypeFactory.unitSort.isTheoryType());
    // despite the name, Int is only a theory type if it was created as such!
    assertFalse(intType().isTheoryType());
  }

  @Test
  void testTypeOrder() {
    assertEquals(0, (new Base("b")).queryTypeOrder());
  }
}

