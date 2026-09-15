/**************************************************************************************************
 Copyright 2025--2026 Cynthia Kop

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

class TVarTest {
  @Test
  void testBasics() {
    Type t = new TVar("β");
    assertFalse(t.isBaseType());
    assertFalse(t.isArrowType());
    assertFalse(t.isDataType());
    assertTrue(t.isVariableType());
    assertFalse(t.isSort());
    assertFalse(t.isSimple());
    assertFalse(t.isMonomorphic());
    assertFalse(t.isZeroSort());
    assertTrue(t.equals(new TVar("β")));
    assertFalse(t.equals(new TVar("δ")));
    assertFalse(t.equals("$β"));
    assertTrue(t.toString().equals("$β"));
    assertTrue(t.queryArity() == 0);
    assertTrue(t.queryNumberSubtypes() == 0);
    assertTrue(t.queryOutputType() == t);
    assertTrue(t.queryTypeOrder() == Integer.MAX_VALUE);
  }

  @Test
  public void testNullCreation() {
    assertThrows(NullStorageException.class, () -> new TVar(null));
  }

  @Test
  public void testComparison() {
    Type y = new TVar("y");
    Type x = new TVar("x");
    Type z = new Base("z");
    Type xz = new Arrow(x, z);
    Type d = TypeFactory.createSort("d", z, x);
    assertTrue(y.compareTo(x) > 0);
    assertTrue(x.compareTo(y) < 0);
    assertTrue(y.compareTo(z) > 0);
    assertTrue(y.compareTo(xz) < 0);
    assertTrue(y.compareTo(d) < 0);
  }

  @Test
  public void testStoreTypeVariables() {
    TreeSet<TVar> set = new TreeSet<TVar>();
    Type x = new TVar("x");
    x.storeTypeVariables(set);
    assertTrue(set.size() == 1);
    assertTrue(set.contains(x));
  }

  @Test
  public void testSubstitute() {
    Type a = new TVar("alpha");
    TestSubstitution map = new TestSubstitution();
    map.extend(new TVar("beta"), new Base("a"));
    assertTrue(a.substitute(map) == a);
    map.extend(new TVar("alpha"), null);
    assertTrue(a.substitute(map) == a);
    Base b = new Base("b");
    map.extend(new TVar("alpha"), b);
    assertTrue(a.substitute(map) == b);
  }

  @Test
  public void testMatch() {
    TVar a = new TVar("alpha");
    TVar b = new TVar("beta");
    TestSubstitution map = new TestSubstitution();

    assertTrue(a.match(new Base("b"), map));
    assertTrue(a.match(new Base("b"), map));
    assertFalse(a.match(new Base("c"), map));
    assertTrue(map.size() == 1);
    assertTrue(map.get(a).equals(new Base("b")));

    assertTrue(b.match(a, map));
    assertTrue(map.get(b).equals(a));
    assertFalse(b.match(new Arrow(new Base("x"), new Base("y")), map));
  }

  @Test
  public void testHashCode() {
    TVar a = new TVar("alpha");
    TVar b = new TVar("alpha");
    assertTrue(a.hashCode() == b.hashCode());
  }
}
