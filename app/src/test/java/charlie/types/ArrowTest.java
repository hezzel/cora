/**************************************************************************************************
 Copyright 2023--2026 Cynthia Kop

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
import java.util.TreeSet;

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
  void testBasics() {
    Type t = new Arrow(intType(), boolType());
    assertTrue(t.isArrowType());
    assertFalse(t.isBaseType());
    assertFalse(t.isDataType());
    assertFalse(t.isVariableType());
    assertFalse(t.isSort());
    assertTrue(t.isSimple());
    assertTrue(t.isMonomorphic());
    assertTrue(t.queryNumberSubtypes() == 2); 
    Type t2 = new Arrow(boolType(), t); 
    assertTrue(t2.querySubtype(1).equals(boolType()));
    assertTrue(t2.querySubtype(2).equals(t));
    assertTrue(t.queryOutputType().equals(boolType()));
  }

  @Test
  public void testSimple() {
    Type inttype = intType();
    Type booltype = boolType();
    Type tuple = new Data("prod", FixedList.of(inttype, inttype));
    Type t = new Arrow(booltype, booltype);
    assertTrue(t.isSimple());
    t = new Arrow(new Arrow(tuple, booltype), inttype);
    assertFalse(t.isSimple());
    t = new Arrow(inttype, new Arrow(booltype, tuple));
    assertFalse(t.isSimple());
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
  public void testArity() {
    Type inttype  = intType();
    Base booltype = boolType();
    Type pair = TypeFactory.createSort("c", inttype, new Arrow(booltype, inttype));
    Type pairbooltype    = new Arrow(pair, booltype);          // c(int, bool -> int) -> bool
    Type intpairbooltype = new Arrow(inttype, pairbooltype);   // int -> c(int, bool -> int) -> bool
    Type intboolpairtype = new Arrow(inttype, new Arrow(booltype, pair));
                                                               // int -> bool -> c(int, bool -> int)

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
    Type pair = TypeFactory.createSort("c", inttype, new Arrow(booltype, inttype));
    Type pairbooltype    = new Arrow(pair, booltype);          // c(int, bool -> int) -> bool
    Type intpairbooltype = new Arrow(inttype, pairbooltype);   // int -> c(int, bool -> int) -> bool
    Type intboolpairtype = new Arrow(inttype, new Arrow(booltype, pair));
                                                               // int -> bool -> c(int, bool -> int)
    assertEquals(1, intintbooltype.queryTypeOrder());
    assertEquals(2, intboolinttype.queryTypeOrder());
    assertEquals(2, pairbooltype.queryTypeOrder());
    assertEquals(2, intpairbooltype.queryTypeOrder());
    assertEquals(1, intboolpairtype.queryTypeOrder());

    Type alpha = new TVar("α");
    Type intalpha = new Arrow(inttype, alpha);
    Type boolalphaint = new Arrow(booltype, new Arrow(alpha, inttype));
    assertTrue(intalpha.queryTypeOrder() == Integer.MAX_VALUE);
    assertTrue(boolalphaint.queryTypeOrder() == Integer.MAX_VALUE);
  }

  @Test
  public void testComparison() {
    Type x = new Base("x");
    Type y = new Base("y");
    Type a = new TVar("a");
    Type xy = new Arrow(x, y);
    Type yx = new Arrow(y, x);
    Type yy = new Arrow(y, y);
    Type d = TypeFactory.createSort("d", a);
    assertTrue(xy.compareTo(x) > 0);
    assertTrue(xy.compareTo(a) > 0);
    assertTrue(xy.compareTo(d) < 0);
    assertTrue(xy.compareTo(yx) > 0); // second argument is compared first
    assertTrue(xy.compareTo(yy) < 0); // if that fails, the first argument is compared
    assertTrue(xy.compareTo(xy) == 0);
    assertTrue(yx.compareTo(xy) < 0);
    assertTrue(yy.compareTo(xy) > 0);
  }

  @Test
  public void testStoreTypeVariables() {
    Type arr = new Arrow(TypeFactory.createSort("c", new TVar("α")), new TVar("β"));
    TreeSet<TVar> set = new TreeSet<TVar>();
    arr.storeTypeVariables(set);
    assertTrue(set.size() == 2);
  }

  @Test
  public void testInstantiate() {
    Type arr = new Arrow(TypeFactory.createSort("c", new TVar("α"), new TVar("β")),
                         new TVar("β"));
    TestSubstitution map = new TestSubstitution();
    map.extend(new TVar("α"), new Base("b"));
    map.extend(new TVar("β"), new Base("a"));
    assertTrue(arr.substitute(map).toString().equals("c(b, a) → a"));
    assertTrue(arr.toString().equals("c($α, $β) → $β"));  // unchanged by the call
  }

  @Test
  public void testMatch() {
    Type arr = new Arrow(new Arrow(new TVar("α"), new TVar("β")), new TVar("β"));

    TestSubstitution map = new TestSubstitution();
    Type lst = TypeFactory.createSort("list", new TVar("δ"));
    Type matches = new Arrow(new Arrow(lst, new Base("a")), new Base("a"));
    assertTrue(arr.match(matches, map));
    assertTrue(map.size() == 2);
    assertTrue(map.get(new TVar("α")).toString().equals("list($δ)"));
    assertTrue(map.get(new TVar("β")).equals(new Base("a")));

    map = new TestSubstitution();
    assertFalse(arr.match(lst, map));
    assertTrue(map.size() == 0);
    assertFalse(arr.match(new Arrow(new Base("base"), new Base("other")), map));

    map = new TestSubstitution();
    assertFalse(arr.match(new Arrow(new Arrow(new Base("a"), new Base("b")), new TVar("δ")), map));
  }

  @Test
  public void testHashCode() {
    Arrow abc1 = new Arrow(new Arrow(new Base("a"), new Base("b")), new Base("c"));
    Arrow abc2 = new Arrow(new Arrow(new Base("a"), new Base("b")), new Base("c"));
    assertTrue(abc1.hashCode() == abc2.hashCode());
  }
}
