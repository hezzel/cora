package cora.types;

import com.google.common.collect.ImmutableList;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.ProdTypeConstructionError;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;

class ProductTest {
  @Test
  void testConstructedWithNull() {
    ArrayList<Type> args = new ArrayList<Type>();
    args.add(new Base("x"));
    args.add(new Base("y"));
    ImmutableList<Type> lst = null;
    Assertions.assertThrows(NullInitialisationError.class, () -> {
      new Product(lst);
      TypeFactory.createProduct(args);
      new Product(ImmutableList.copyOf(args));
      TypeFactory.createProduct(ImmutableList.copyOf(args));
      TypeFactory.createProduct(null, new Base("z"));
      TypeFactory.createProduct(new Base("z"), new Base("q"), null);
    });
  }

  @Test
  public void testConstructedTooShort() {
    ImmutableList.Builder builder = ImmutableList.builder();
    ImmutableList<Type> l0 = builder.build();
    builder = ImmutableList.builder();
    builder.add(new Arrow(new Base("a"), new Base("b")));
    ImmutableList<Type> l1 = builder.build();
    Assertions.assertThrows(ProdTypeConstructionError.class, () -> {
      new Product(l0);
      new Product(l1);
    });
  }

/*
  @Test
  void tesMethodTypeReturn(){
    Type arrType = TypeFactory.createArrow(intType(), boolType());
    assertFalse(arrType.isTheoryType());
    assertTrue(arrType.isArrowType());
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
    assertTrue(at1.toString().equals("Bool ⇒ Int"));
    assertTrue(at2.toString().equals("(Bool ⇒ Int) ⇒ Array"));
    assertTrue(at3.toString().equals("(Bool ⇒ Int) ⇒ Bool ⇒ Int"));
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
  public void testTypeOrder() {
    Type inttype  = intType();
    Base booltype = boolType();
    Type intbooltype    = new Arrow(inttype, booltype);        // int -> bool
    Type intintbooltype = new Arrow(inttype, intbooltype);     // int -> int -> bool
    Type intboolinttype = new Arrow(intbooltype, inttype);     // (int -> bool) -> int

    assertEquals(1, intintbooltype.queryTypeOrder());
    assertEquals(2, intboolinttype.queryTypeOrder());
  }
*/
}
