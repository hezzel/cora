/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

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
import charlie.util.FixedList;

class ArrowTest {
  private Base intType() {
    return new Base("Int");
  }

  private Base boolType() {
    return new Base("Bool");
  }

  @Test
  void testConstructedWithNull() {
    assertThrows(NullStorageException.class, () -> {
      new Arrow(null, new Base(""));
      new Arrow(new Base(""), null);
    });
  }

  @Test
  void tesMethodTypeReturn(){
    Type arrType = TypeFactory.createArrow(intType(), boolType());
    assertFalse(arrType.isTheoryType());
    assertTrue(arrType.isArrowType());
  }

  @Test
  void testBasics() {
    Type t = new Arrow(intType(), boolType());
    assertTrue(t.isArrowType());
    assertFalse(t.isBaseType());
    assertFalse(t.isProductType());
  }

  @Test
  public void testHasProducts() {
    Type inttype = intType();
    Type booltype = boolType();
    Type tuple = new Product(FixedList.of(inttype, inttype));
    Type t = new Arrow(booltype, booltype);
    assertFalse(t.hasProducts());
    t = new Arrow(new Arrow(tuple, booltype), inttype);
    assertTrue(t.hasProducts());
    t = new Arrow(inttype, new Arrow(booltype, tuple));
    assertTrue(t.hasProducts());
  }

  @Test
  public void testEquality() {
    Type inttype = intType();
    Type booltype = boolType();
    Arrow ib = new Arrow(inttype, booltype);
    Arrow bb = new Arrow(booltype, booltype);
    Arrow ibb1 = new Arrow(ib, booltype);
    Arrow ibb2 = new Arrow(inttype, bb);

    assertFalse(inttype.equals(ib));
    assertFalse(ib.equals(inttype));
    assertTrue(ib.equals(ib));
    assertTrue(ib.equals(new Arrow(intType(), booltype)));
    assertFalse(ib.equals(bb));
    assertFalse(ibb1.equals(ibb2));
  }

  @Test
  public void testToString() {
    Arrow at1 = new Arrow(boolType(), intType());
    Arrow at2 = new Arrow(at1, new Base("Array"));
    Arrow at3 = new Arrow(at1, at1);
    assertTrue(at1.toString().equals("Bool → Int"));
    assertTrue(at2.toString().equals("(Bool → Int) → Array"));
    assertTrue(at3.toString().equals("(Bool → Int) → Bool → Int"));
  }

  @Test
  public void testTheory() {
    Arrow abc =
      new Arrow(new Arrow(new Base("a"), new Base("b")), new Base("c"));
    assertFalse(abc.isTheoryType());
    Arrow ib = new Arrow(UniqueTypes.boolSort, UniqueTypes.intSort);
    assertTrue(ib.isTheoryType());
  }

  @Test
  public void testArity() {
    Type inttype  = intType();
    Base booltype = boolType();
    Type pair = TypeFactory.createProduct(inttype, new Arrow(booltype, inttype));
    Type pairbooltype    = new Arrow(pair, booltype);          // (int x bool -> int) -> bool
    Type intpairbooltype = new Arrow(inttype, pairbooltype);   // int -> (int x bool -> int) -> bool
    Type intboolpairtype = new Arrow(inttype, new Arrow(booltype, pair));
                                                               // int -> bool -> (int x (bool -> int))

    assertTrue(pairbooltype.queryArity() == 1);
    assertTrue(intpairbooltype.queryArity() == 2);
    assertTrue(intboolpairtype.queryArity() == 2);
  }

  @Test
  public void testTypeOrder() {
    Type inttype  = intType();
    Base booltype = boolType();
    Type intbooltype    = new Arrow(inttype, booltype);        // int -> bool
    Type intintbooltype = new Arrow(inttype, intbooltype);     // int -> int -> bool
    Type intboolinttype = new Arrow(intbooltype, inttype);     // (int -> bool) -> int
    Type pair = TypeFactory.createProduct(inttype, new Arrow(booltype, inttype));
    Type pairbooltype    = new Arrow(pair, booltype);          // (int x bool -> int) -> bool
    Type intpairbooltype = new Arrow(inttype, pairbooltype);   // int -> (int x bool -> int) -> bool
    Type intboolpairtype = new Arrow(inttype, new Arrow(booltype, pair));
                                                               // int -> bool -> (int x (bool -> int))
    assertEquals(1, intintbooltype.queryTypeOrder());
    assertEquals(2, intboolinttype.queryTypeOrder());
    assertEquals(2, pairbooltype.queryTypeOrder());
    assertEquals(2, intpairbooltype.queryTypeOrder());
    assertEquals(1, intboolpairtype.queryTypeOrder());
  }

  @Test
  public void testHashCode() {
    Arrow abc1 = new Arrow(new Arrow(new Base("a"), new Base("b")), new Base("c"));
    Arrow abc2 = new Arrow(new Arrow(new Base("a"), new Base("b")), new Base("c"));
    assertTrue(abc1.hashCode() == abc2.hashCode());
  }
}
