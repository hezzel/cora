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

package charlie.terms;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.util.FixedList;
import charlie.util.NullStorageException;
import charlie.types.Type;
import charlie.parser.CoraParser;
import charlie.terms.replaceable.Replaceable;

public class HigherMetaVarTest {
  private FixedList<Type> fili(Type type1, Type type2) {
    FixedList.Builder<Type> builder = new FixedList.Builder<Type>();
    if (type1 != null) builder.add(type1);
    if (type2 != null) builder.add(type2);
    return builder.build();
  }

  private Type type(String desc) { return CoraParser.readType(desc); }

  @Test
  public void testCreateWithNullName() {
    assertThrows(NullStorageException.class, () ->
      new HigherMetaVar(null, fili(type("a"), type("b")), type("c")));
  }

  @Test
  public void testCreateWithNullInputs() {
    assertThrows(NullStorageException.class, () ->
      new HigherMetaVar("z", null, type("c")));
  }

  @Test
  public void testCreateWithSingleNullInput() {
    assertThrows(NullStorageException.class, () -> TermFactory.createMetaVar("z",
      type("a"), null, type("c")));
  }

  @Test
  public void testCreateWithNullOutput() {
    assertThrows(NullStorageException.class,
      () -> new HigherMetaVar("z", fili(type("a"), type("b")), null));
  }

  @Test
  public void testCreateWithEmptyInputs() {
    assertThrows(IllegalArgumentException.class, () ->
      new HigherMetaVar("z", fili(null, null), type("c")));
  }

  @Test
  public void testCorrectCreation() {
    Type a = type("a"), b = type("b");
    MetaVariable z = TermFactory.createMetaVar("z", fili(a, b), type("c"));
    assertTrue(z.queryName().equals("z"));
    assertTrue(z.queryArity() == 2);
    assertTrue(z.queryInputType(1).equals(type("a")));
    assertTrue(z.queryInputType(2).equals(type("b")));
    assertTrue(z.queryOutputType().equals(type("c")));
    assertTrue(z.queryType().toString().equals("a → b → c"));
    assertTrue(z.equals(z));
    MetaVariable z2 = TermFactory.createMetaVar("z", a, b, type("c"));
    assertFalse(z.equals(z2));
    assertTrue(z.toString().equals("z"));
  }

  @Test
  public void testFactoryCreation() {
    Type type = type("a -> b -> c -> d -> e");
    MetaVariable x = TermFactory.createMetaVar("xx", type, 3);
    assertTrue(x.queryName().equals("xx"));
    assertTrue(x.queryArity() == 3);
    assertTrue(x.queryReplaceableKind() == Replaceable.Kind.METAVAR);
    assertTrue(x.queryInputType(1).equals(type("a")));
    assertTrue(x.queryInputType(2).equals(type("b")));
    assertTrue(x.queryInputType(3).equals(type("c")));
    assertTrue(x.queryOutputType().toString().equals("d → e"));
    assertTrue(x.queryType().equals(type));
  }

  @Test
  public void testMetavarIndexes() {
    Type a = type("a"), b = type("b");
    MetaVariable z1 = TermFactory.createMetaVar("z", fili(a,b), type("c"));
    MetaVariable z2 = TermFactory.createMetaVar("z", fili(a,b), type("c"));
    assertTrue(z1.queryIndex() < z2.queryIndex());
    assertTrue(z1.compareTo(z2) == -1);
    assertTrue(z2.compareTo(z1) == 1);
  }

  @Test
  public void testMakeTerm() {
    Type a = type("a"), b = type("b");
    MetaVariable z = TermFactory.createMetaVar("Z", fili(a,b), type("c"));
    Term t = TermFactory.makeTerm(z);
    assertTrue(t.toString().equals("λb1.λb2.Z⟨b1, b2⟩"));
  }

  @Test
  public void testMetavarComparison() {
    Type a = type("a"), b = type("b");
    Replaceable z = TermFactory.createMetaVar("z", fili(a,b), type("c"));
    Replaceable x = new Var("z", z.queryType());
    Replaceable y = new Binder("z", x.queryType());
    assertTrue(z.compareTo(z) == 0);
    assertTrue(z.compareTo(x) < 0);
    assertTrue(z.compareTo(y) < 0);
    assertTrue(x.compareTo(z) > 0);
    assertTrue(y.compareTo(z) > 0);
    assertTrue(z.hashCode() == z.hashCode());
    assertFalse(z.hashCode() == x.hashCode());
    assertFalse(z.hashCode() == y.hashCode());
    Replaceable zz = TermFactory.createMetaVar("z", fili(a,b), type("c"));
    assertFalse(z.hashCode() == zz.hashCode());
  }
}
