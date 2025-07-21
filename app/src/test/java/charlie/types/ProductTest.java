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
import java.util.ArrayList;

import charlie.util.FixedList;
import charlie.util.NullStorageException;

class ProductTest {
  @Test
  void testConstructedWithNull() {
    ArrayList<Type> args = new ArrayList<Type>();
    args.add(new Base("x"));
    args.add(new Base("y"));
    args.add(null);
    FixedList<Type> lst = null;

    assertThrows(NullStorageException.class, () -> new Product(lst));
    assertThrows(charlie.util.NullStorageException.class,
      () -> TypeFactory.createProduct(args));
    assertThrows(charlie.util.NullStorageException.class,
      () -> new Product(FixedList.copy(args)));
    assertThrows(charlie.util.NullStorageException.class,
      () -> TypeFactory.createProduct(FixedList.copy(args)));
    assertThrows(charlie.util.NullStorageException.class,
      () -> TypeFactory.createProduct(null, new Base("z")));
    assertThrows(charlie.util.NullStorageException.class,
      () -> TypeFactory.createProduct(new Base("z"), new Base("q"), null));
  }

  @Test
  public void testConstructedTooShort() {
    FixedList.Builder<Type> builder = new FixedList.Builder<Type>();
    FixedList<Type> l0 = builder.build();
    builder = new FixedList.Builder<Type>();
    builder.add(new Arrow(new Base("a"), new Base("b")));
    FixedList<Type> l1 = builder.build();
    assertThrows(IllegalArgumentException.class, () -> new Product(l0));
    assertThrows(IllegalArgumentException.class, () -> new Product(l1));
  }

  @Test
  public void testBasics() {
    Type prod = TypeFactory.createProduct(new Base("a"), new Arrow(new Base("b"), new Base("c")));
    Type prod2 = TypeFactory.createProduct(new Base("a"), new Base("b"), new Base("c"));
    assertTrue(prod.isProductType());
    assertFalse(prod.isBaseType());
    assertFalse(prod2.isBaseType());
    assertFalse(prod.isArrowType());
    assertTrue(prod.queryArity() == 0);
    assertTrue(prod.queryOutputType() == prod);
    assertTrue(prod.hasProducts());
  }

  @Test
  public void testTheory() {
    Type prod = TypeFactory.createProduct(TypeFactory.intSort,
      new Arrow(TypeFactory.stringSort, TypeFactory.boolSort), TypeFactory.boolSort);
    assertTrue(prod.isTheoryType());
    prod = TypeFactory.createProduct(TypeFactory.intSort, TypeFactory.defaultSort);
    assertFalse(prod.isTheoryType());
  }

  @Test
  public void testEquality() {
    Type a = new Base("a");
    Type b = new Base("b");
    Type c = new Base("c");
    // a × b × c
    Type plain = TypeFactory.createProduct(a, b, c);
    // (a × b) × c
    Type left = TypeFactory.createProduct(TypeFactory.createProduct(a, b), c);
    // a × (b × c)
    Type right = TypeFactory.createProduct(a, TypeFactory.createProduct(b, c));
    // c × b × a
    Type plain2 = TypeFactory.createProduct(c, b, a);

    assertTrue(plain.equals(TypeFactory.createProduct(a, b, c)));
    assertFalse(plain.equals(left));
    assertFalse(plain.equals(right));
    assertFalse(plain.equals(plain2));
    assertFalse(left.equals(right));
  }

  @Test
  public void testToString() {
    Type a = new Base("a");
    Type b = new Base("b");
    Type c = new Base("c");
    Type d = new Base("d");
    // ⦇ a, b, c ⦈
    Type abc = TypeFactory.createProduct(a, b, c);
    // ⦇ ⦇ a, b ⦈, ⦇ c, d ⦈ ⦈
    Type abcd = TypeFactory.createProduct(TypeFactory.createProduct(a, b),
                                          TypeFactory.createProduct(c, d));
    // ⦇ a -> b, × c ⦈
    Type aarrbc = TypeFactory.createProduct(new Arrow(a, b), c);
    // ⦇ a, b ⦈ -> c
    Type atimesbc = new Arrow(TypeFactory.createProduct(a, b), c);

    assertTrue(abc.toString().equals("⦇ a, b, c ⦈"));
    assertTrue(abcd.toString().equals("⦇ ⦇ a, b ⦈, ⦇ c, d ⦈ ⦈"));
    assertTrue(aarrbc.toString().equals("⦇ a → b, c ⦈"));
    assertTrue(atimesbc.toString().equals("⦇ a, b ⦈ → c"));
  }

  @Test
  public void testTypeOrder() {
    Type a = new Base("a");
    Type b = new Base("b");
    Type c = new Base("c");
    Type d = new Base("d");
    // a x b
    Type simple = TypeFactory.createProduct(a, b);
    // a x (b -> c) x d
    Type complex = TypeFactory.createProduct(a, new Arrow(b, c), d);

    assertEquals(0, simple.queryTypeOrder());
    assertEquals(1, complex.queryTypeOrder());
  }

  @Test
  public void testHashCode() {
    Type a = new Base("a");
    Type b = new Base("b");
    Type c = new Base("c");
    Type d = new Base("d");
    // a x (b -> c) x d
    Type type1 = TypeFactory.createProduct(a, new Arrow(b, c), d);
    Type type2 = TypeFactory.createProduct(a, new Arrow(b, c), new Base("d"));
    assertTrue(type1.hashCode() == type2.hashCode());
  }
}
