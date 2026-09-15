/**************************************************************************************************
 Copyright 2019--2026 Cynthia Kop

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
    assertFalse(t.isDataType());
    assertFalse(t.isVariableType());
    assertTrue(t.isSort());
    assertTrue(t.isSimple());
    assertTrue(t.isMonomorphic());
    assertTrue(t.equals(t));
    assertTrue(t.equals(intType()));
    assertFalse(t.equals(boolType()));
    assertFalse(t.equals(new TVar("Int")));
    assertFalse(t.equals("Int"));
    assertTrue(t.toString().equals("Int"));
    assertTrue(t.queryArity() == 0); 
    assertTrue(t.queryNumberSubtypes() == 0); 
    assertTrue(t.queryOutputType() == t); 
  }

  @Test
  void testToStringIsJustTheName() {
    String name = java.util.UUID.randomUUID().toString();

    Type ty = new Base(name);
    assertEquals(name, ty.toString());
  }

  @Test
  void testTypeOrder() {
    assertEquals(0, (new Base("b")).queryTypeOrder());
  }

  @Test
  public void testComparison() {
    Type x = new Base("x");
    Type a = new Base("a");
    Type aa = new Arrow(a, a);
    Type b = new TVar("b");
    Type d = TypeFactory.createSort("d", a);
    assertTrue(x.compareTo(a) > 0);
    assertTrue(a.compareTo(x) < 0);
    assertTrue(x.compareTo(aa) < 0);
    assertTrue(x.compareTo(b) < 0);
    assertTrue(x.compareTo(d) < 0);
  }

  @Test
  public void testInstantiate() {
    Type a = new Base("sort");
    TestSubstitution map = new TestSubstitution();
    map.extend(new TVar("sort"), new Base("a"));
    assertTrue(a.substitute(map) == a);
  }

  @Test
  public void testMatch() {
    Type a = new Base("sort");
    TestSubstitution map = new TestSubstitution();
    assertTrue(a.match(new Base("sort"), map));
    assertFalse(a.match(new Base("a"), map));
    assertFalse(a.match(new TVar("sort"), map));
    assertFalse(a.match(TypeFactory.createSort("sort", new Base("a")), map));
    assertFalse(a.match(new Arrow(a, a), map));
    assertTrue(map.size() == 0);
  }

  @Test
  public void testHashCode() {
    Base a = new Base("A");
    Base b = new Base("A");
    assertTrue(a.hashCode() == b.hashCode());
  }
}
