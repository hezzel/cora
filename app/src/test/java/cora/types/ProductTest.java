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
    args.add(null);
    ImmutableList<Type> lst = null;

    Assertions.assertThrows(NullInitialisationError.class, () -> new Product(lst));
    // NullPointerException instead of NullInitialisationError due to ImmutableList
    // blocking null elements
    Assertions.assertThrows(java.lang.NullPointerException.class,
      () -> TypeFactory.createProduct(args));
    Assertions.assertThrows(java.lang.NullPointerException.class,
      () -> new Product(ImmutableList.copyOf(args)));
    Assertions.assertThrows(java.lang.NullPointerException.class,
      () -> TypeFactory.createProduct(ImmutableList.copyOf(args)));
    Assertions.assertThrows(java.lang.NullPointerException.class,
      () -> TypeFactory.createProduct(null, new Base("z")));
    Assertions.assertThrows(java.lang.NullPointerException.class,
      () -> TypeFactory.createProduct(new Base("z"), new Base("q"), null));
  }

  @Test
  public void testConstructedTooShort() {
    ImmutableList.Builder builder = ImmutableList.builder();
    ImmutableList<Type> l0 = builder.build();
    builder = ImmutableList.builder();
    builder.add(new Arrow(new Base("a"), new Base("b")));
    ImmutableList<Type> l1 = builder.build();
    Assertions.assertThrows(ProdTypeConstructionError.class, () -> new Product(l0));
    Assertions.assertThrows(ProdTypeConstructionError.class, () -> new Product(l1));
  }

  @Test
  public void testBasics() {
    Type prod = TypeFactory.createProduct(new Base("a"), new Arrow(new Base("b"), new Base("c")));
    Type prod2 = TypeFactory.createProduct(new Base("a"), new Base("b"), new Base("c"));
    assertTrue(prod.isProdType());
    assertFalse(prod.isBaseType());
    assertFalse(prod2.isBaseType());
    assertFalse(prod.isArrowType());
    assertTrue(prod.queryArity() == 0);
    assertTrue(prod.queryOutputType() == prod);
  }

  @Test
  public void testTheory() {
    Type prod = TypeFactory.createProduct(TypeFactory.intSort,
      new Arrow(TypeFactory.stringSort, TypeFactory.boolSort), TypeFactory.boolSort);
    assertTrue(prod.isTheoryType());
    prod = TypeFactory.createProduct(TypeFactory.intSort, TypeFactory.unitSort);
    assertFalse(prod.isTheoryType());
  }

  @Test
  public void testEquality() {
    Type a = new Base("a");
    Type b = new Base("b");
    Type c = new Base("c");
    // a x b x c
    Type plain = TypeFactory.createProduct(a, b, c);
    // (a x b) x c
    Type left = TypeFactory.createProduct(TypeFactory.createProduct(a, b), c);
    // a x (b x c)
    Type right = TypeFactory.createProduct(a, TypeFactory.createProduct(b, c));
    // c x b x a
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
    // a x b x c
    Type abc = TypeFactory.createProduct(a, b, c);
    // (a x b) x (c x d)
    Type abcd = TypeFactory.createProduct(TypeFactory.createProduct(a, b),
                                          TypeFactory.createProduct(c, d));
    // (a -> b) x c
    Type aarrbc = TypeFactory.createProduct(new Arrow(a, b), c);
    // (a x b) -> c
    Type atimesbc = new Arrow(TypeFactory.createProduct(a, b), c);

    assertTrue(abc.toString().equals("a x b x c"));
    assertTrue(abcd.toString().equals("(a x b) x (c x d)"));
    assertTrue(aarrbc.toString().equals("(a ⇒ b) x c"));
    assertTrue(atimesbc.toString().equals("(a x b) ⇒ c"));
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
}
