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

public class ArrowTypeTest {
  private BaseType intType() {
    return new Sort("Int");
  }

  private BaseType boolType() {
    return new Sort("Bool");
  }

  @Test(expected = NullInitialisationError.class)
  public void testConstructedWithNullInput() {
    Type y = new ArrowType(null, boolType());
  }

  @Test(expected = NullInitialisationError.class)
  public void testConstructedWithNullOutput() {
    Type y = new ArrowType(intType(), null);
  }

  @Test
  public void testEquality() {
    Type inttype = intType();
    Type booltype = boolType();
    ArrowType ib = new ArrowType(inttype, booltype);
    ArrowType bb = new ArrowType(booltype, booltype);
    ArrowType ibb1 = new ArrowType(ib, booltype);
    ArrowType ibb2 = new ArrowType(inttype, bb);

    assertFalse(inttype.equals(ib));
    assertFalse(ib.equals(inttype));
    assertFalse(ib.equals(null));
    assertTrue(ib.equals(ib));
    assertTrue(ib.equals(new ArrowType(intType(), booltype)));
    assertFalse(ib.equals(bb));
    assertFalse(ibb1.equals(ibb2));
  }

  @Test
  public void testToString() {
    ArrowType at1 = new ArrowType(boolType(), intType());
    ArrowType at2 = new ArrowType(at1, new Sort("Array"));
    ArrowType at3 = new ArrowType(at1, at1);
    assertTrue(at1.toString().equals("Bool ⇒ Int"));
    assertTrue(at2.toString().equals("(Bool ⇒ Int) ⇒ Array"));
    assertTrue(at3.toString().equals("(Bool ⇒ Int) ⇒ Bool ⇒ Int"));
  }

  @Test
  public void testAppendInputTypes() {
    ArrowType intermediate = new ArrowType(intType(), boolType());
    ArrowType at = new ArrowType(intType(), new ArrowType(intermediate, boolType()));
    ArrayList<Type> args = new ArrayList<Type>();
    at.appendInputTypes(args);
    assertEquals(2, args.size());
    assertTrue(args.get(0).equals(intType()));
    assertTrue(args.get(1).equals(intermediate));
  }

  @Test
  public void testTrivialities() {
    Type inttype = intType();
    BaseType booltype = boolType();
    Type intbooltype = new ArrowType(inttype, booltype);
    Type intintbooltype = new ArrowType(inttype, intbooltype);
    Type intboolinttype = new ArrowType(intbooltype, inttype);

    assertEquals(2, intintbooltype.queryArity());
    assertEquals(1, intboolinttype.queryArity());
    assertTrue(intbooltype.isArrowType());
    assertFalse(intbooltype.isBaseType());
    assertTrue(intboolinttype.queryArrowInputType().equals(intbooltype));
    assertTrue(intboolinttype.queryArrowOutputType().equals(inttype));
    assertTrue(intintbooltype.queryArrowInputType().equals(inttype));
    assertTrue(intintbooltype.queryArrowOutputType().equals(intbooltype));
    assertTrue(intintbooltype.queryOutputSort().equals(booltype));
  }

  @Test
  public void testTypeOrder() {
    Type inttype = intType();
    BaseType booltype = boolType();
    Type intbooltype = new ArrowType(inttype, booltype);        // int -> bool
    Type intintbooltype = new ArrowType(inttype, intbooltype);  // int -> int -> bool
    Type intboolinttype = new ArrowType(intbooltype, inttype);  // (int -> bool) -> int

    assertEquals(1, intintbooltype.queryTypeOrder());
    assertEquals(2, intboolinttype.queryTypeOrder());
  }
}
