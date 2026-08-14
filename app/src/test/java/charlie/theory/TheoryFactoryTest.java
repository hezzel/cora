/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.theory;

import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.types.TypeFactory;

public class TheoryFactoryTest {
  @Test
  public void testIntegerValues() {
    TreeSet<IntegerValue> set = new TreeSet<IntegerValue>();
    IntegerValue v = TheoryFactory.getNewIntegerValue(set);
    assertTrue(v.getInteger().intValueExact() == 0);
    set.add(v);
    v = TheoryFactory.getNewIntegerValue(set);
    assertTrue(v.getInteger().intValueExact() == 1);
    set.add(v);
    v = TheoryFactory.getNewIntegerValue(set);
    assertTrue(v.getInteger().intValueExact() == -1);
    set.add(v);
    v = TheoryFactory.getNewIntegerValue(set);
    assertTrue(v.getInteger().intValueExact() == 2);
    set.add(v);
    v = TheoryFactory.getNewIntegerValue(set);
    assertTrue(v.getInteger().intValueExact() == -2);
    set.add(v);
    v = TheoryFactory.getNewIntegerValue(set);
    assertTrue(v.getInteger().intValueExact() == 3);
  }

  @Test
  public void testStringValues() {
    TreeSet<StringValue> set = new TreeSet<StringValue>();
    StringValue v = TheoryFactory.getNewStringValue(set);
    assertTrue(v.getString().equals(""));
    set.add(v);
    v = TheoryFactory.getNewStringValue(set);
    assertTrue(v.getString().equals("a"));
    set.add(v);
    v = TheoryFactory.getNewStringValue(set);
    assertTrue(v.getString().equals("b"));
    set.add(v);
    for (int i = 0; i < 24; i++) set.add(TheoryFactory.getNewStringValue(set));
    v = TheoryFactory.getNewStringValue(set);
    assertTrue(v.getString().equals("aa"));
    set.add(v);
    v = TheoryFactory.getNewStringValue(set);
    assertTrue(v.getString().equals("ba"));
  }

  @Test
  public void testBooleanValues() {
    TreeSet<Value> set = new TreeSet<Value>();
    set.add(TheoryFactory.zeroValue);
    Value v = TheoryFactory.getNewValue(TypeFactory.boolSort, set);
    assertTrue(Theory.toBooleanValue(v).getBool());
    set.add(v);
    v = TheoryFactory.getNewValue(TypeFactory.boolSort, set);
    assertFalse(Theory.isTrue(v));
    set.add(v);
    v = TheoryFactory.getNewValue(TypeFactory.boolSort, set);
    assertTrue(v == null);
  }
}
