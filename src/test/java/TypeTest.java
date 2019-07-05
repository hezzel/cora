/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import org.junit.Test;
import static org.junit.Assert.*;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import java.util.ArrayList;
import cora.interfaces.types.*;
import cora.immutabledata.types.*;

public class TypeTest {
  private BaseType intType() {
    return new Sort("Int");
  }

  private BaseType boolType() {
    return new Sort("Bool");
  }

  @Test(expected = NullInitialisationError.class)
  public void testSortConstructionWithNullGivesError() {
    Type x = new Sort(null);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testSortAskedForInputTypeError() {
    intType().queryArrowInputType();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testSortAskedForOutputTypeError() {
    boolType().queryArrowOutputType();
  }

  @Test
  public void testSortToStringIsJustTheName() {
    Type xxx = new Sort("xXx");
    assertTrue(xxx.toString().equals("xXx"));
  }

  @Test
  public void testSortEqualityIsStringEquality() {
    ArrayList<Type> types;

    assertTrue(intType().equals(intType()));
    assertFalse(intType().equals(boolType()));
  }

  @Test
  public void testSortEqualityWithCapitals() {
    Type xxa = new Sort("xXx");
    Type xxb = new Sort("xXx");
    Type xxc = new Sort("xxX");
    assertTrue(xxa.equals(xxb));
    assertFalse(xxa.equals(xxc));
  }

  @Test
  public void testSortOutputTypeIsItself() {
    assertTrue(intType().equals(intType().queryOutputSort()));
  }

  @Test
  public void testSortTypeKindIsBase() {
    assertEquals(intType().queryTypeKind(), Type.TypeKind.BASETYPE);
  }

  @Test
  public void testBaseTypeHasNoInputTypes() {
    Type inttype = intType();
    assertEquals(inttype.queryArity(), 0);
    ArrayList<Type> lst = new ArrayList<Type>();
    inttype.appendInputTypes(lst);
    assertTrue(lst.isEmpty());
  }

  @Test(expected = NullInitialisationError.class)
  public void testArrowTypeConstructedWithNullInput() {
    Type y = new ArrowType(null, boolType());
  }

  @Test(expected = NullInitialisationError.class)
  public void testArrowTypeConstructedWithNullOutput() {
    Type y = new ArrowType(intType(), null);
  }

  @Test
  public void testArrowTypeEquality() {
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
  public void testArrowTypeToString() {
    ArrowType at1 = new ArrowType(boolType(), intType());
    ArrowType at2 = new ArrowType(at1, new Sort("Array"));
    ArrowType at3 = new ArrowType(at1, at1);
    assertTrue(at1.toString().equals("Bool => Int"));
    assertTrue(at2.toString().equals("(Bool => Int) => Array"));
    assertTrue(at3.toString().equals("(Bool => Int) => Bool => Int"));
  }

  @Test
  public void testArrowTypeAppendInputTypes() {
    ArrowType intermediate = new ArrowType(intType(), boolType());
    ArrowType at = new ArrowType(intType(), new ArrowType(intermediate, boolType()));
    ArrayList<Type> args = new ArrayList<Type>();
    at.appendInputTypes(args);
    assertEquals(2, args.size());
    assertTrue(args.get(0).equals(intType()));
    assertTrue(args.get(1).equals(intermediate));
  }

  @Test
  public void testArrowTypeTrivialities() {
    Type inttype = intType();
    BaseType booltype = boolType();
    Type intbooltype = new ArrowType(inttype, booltype);
    Type intintbooltype = new ArrowType(inttype, intbooltype);
    Type intboolinttype = new ArrowType(intbooltype, inttype);

    assertEquals(2, intintbooltype.queryArity());
    assertEquals(1, intboolinttype.queryArity());
    assertTrue(intboolinttype.queryArrowInputType().equals(intbooltype));
    assertTrue(intboolinttype.queryArrowOutputType().equals(inttype));
    assertTrue(intintbooltype.queryArrowInputType().equals(inttype));
    assertTrue(intintbooltype.queryArrowOutputType().equals(intbooltype));
    assertTrue(intintbooltype.queryOutputSort().equals(booltype));
  }
}
