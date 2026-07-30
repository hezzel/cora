/**************************************************************************************************
 Copyright 2024--2026 Cynthia Kop

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
import java.util.Set;
import charlie.types.*;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;

public class NameGeneratorTest {
  @Test
  public void testRenamingWithoutAvoidance() {
    Type a = TypeFactory.createSort("a");
    Type b = TypeFactory.createSort("b");
    Type ab = TypeFactory.createArrow(a, b);
    Variable x1 = new Var("x", a);
    Variable x2 = new Var("x", a);
    Variable x3 = new Binder("x", b);
    MetaVariable mvar = TermFactory.createMetaVar("x", TypeFactory.createArrow(a, a), 1);
    Term x4 = TermFactory.createMeta(mvar, TermFactory.createConstant("A", a));
    Variable y = new Binder("y", b);
    Variable z1 = new Binder("z", ab);
    Variable z2 = new Var("z", ab);
    NameGenerator generator = new NameGenerator(Set.of());
    Renaming naming = generator.generateUniqueNaming(x1, x2, x3, x4, y, z1, z2);
    assertTrue(naming.getName(x1).equals("x__2"));
    assertTrue(naming.getName(x2).equals("x__3"));
    assertTrue(naming.getName(x3).equals("x__4"));
    assertTrue(naming.getName(mvar).equals("x__1"));  // meta-variables come before variables
    assertTrue(naming.getName(y).equals("y"));
    assertTrue(naming.getName(z1).equals("z__2"));  // binders come after non-binders
    assertTrue(naming.getName(z2).equals("z__1"));
  }

  @Test
  public void testBannedOverlap() {
    NameGenerator generator = new NameGenerator(Set.of("x", "y__1", "z", "z__1", "u", "v__1"));
    Type o = TypeFactory.defaultSort;
    Variable x = new Var("x", o);
    Variable y1 = new Var("y", o);
    Variable y2 = new Var("y", o);
    Variable z = new Binder("z", o);
    Variable u1 = new Var("u", o);
    Variable u2 = new Var("u", o);
    Variable v = new Var("v", o);
    Variable w = new Var("", o);
    Variable a = new Var("17", o);
    Variable b1 = new Var("b", o);
    Variable b2 = new Var("b", o);
    Variable b3 = new Var("b__1", o);
    Renaming naming = generator.generateUniqueNaming(x, y1, y2, z, u1, u2, v, w, a, b1, b2, b3);
    assertTrue(naming.getName(x).equals("x__1"));
    assertTrue(naming.getName(y1).equals("y__2"));
    assertTrue(naming.getName(y2).equals("y__3"));
    assertTrue(naming.getName(z).equals("z__2"));
    assertTrue(naming.getName(u1).equals("u__1"));
    assertTrue(naming.getName(u2).equals("u__2"));
    assertTrue(naming.getName(v).equals("v"));
    assertTrue(naming.getName(w).equals("VAR"));
    assertTrue(naming.getName(a).equals("_17"));
    assertTrue(naming.getName(b1).equals("b__2"));
    assertTrue(naming.getName(b2).equals("b__3"));
    assertTrue(naming.getName(b3).equals("b__1"));
  }

  @Test
  public void testBoundVariableRenaming() {
    Type o = TypeFactory.defaultSort;
    Variable x = new Binder("x", o);
    Variable y = new Binder("y", o);
    Term abs1 = new Abstraction(x, x);
    Term abs2 = new Abstraction(y, y);
    Type oo = TypeFactory.createArrow(o, o);
    Term f =
      TermFactory.createConstant("f", TypeFactory.createArrow(oo, TypeFactory.createArrow(oo, o)));
    Term term = TermFactory.createApp(f, abs1, abs2); // f(λx.x, λy.y)

    NameGenerator generator = new NameGenerator(Set.of());
    MutableRenaming naming = generator.generateUniqueNaming(term, x);
    assertTrue(naming.getName(x).equals("x"));
    assertTrue(naming.getName(y) == null);
    assertFalse(naming.isAvailable("x"));
    assertTrue(naming.isAvailable("y"));

    generator.generateBoundName(naming, y);
    assertTrue(naming.getName(y).equals("y"));
  }

  @Test
  public void testIncompleteRenamingUsedWithAbstraction() {
    Type o = TypeFactory.createSort("o");
    // λx.λy.λu.f(g(z2,u),z1,x) where x and u have the same name, and z1 and z2 too
    Variable x = new Binder("x", o);
    Variable y = new Binder("y", o);
    Variable z1 = new Binder("z", o);
    Variable z2 = new Binder("z", o);
    Variable u = new Binder("x", o);
    Constant f = new Constant("f", TypeFactory.createArrow(o, TypeFactory.createArrow(o,
      TypeFactory.createArrow(o, o))));
    Constant g = new Constant("g", TypeFactory.createArrow(o, TypeFactory.createArrow(o, o)));
    Term main = (new Application(f, new Application(g, z2, u), z1)).apply(x);
    Term abs = new Abstraction(x, new Abstraction(y, new Abstraction(u, main)));

    NameGenerator generator = new NameGenerator(Set.of());
    MutableRenaming naming = generator.generateUniqueNaming(abs);

    assertTrue(naming.getName(x) == null);
    assertTrue(naming.getName(y) == null);
    assertTrue(naming.getName(u) == null);
    assertTrue(naming.getName(z1).equals("z__1"));
    assertTrue(naming.getName(z2).equals("z__2"));

    generator.generateBoundName(naming, x);
    generator.generateBoundName(naming, y);
    generator.generateBoundName(naming, u);
    Variable z3 = new Binder("z", o);
    generator.generateBoundName(naming, z3);
    assertTrue(naming.getName(x).equals("x"));
    assertTrue(naming.getName(y).equals("y"));
    assertTrue(naming.getName(u).equals("x__1"));
    assertTrue(naming.getName(z3).equals("z__3"));
  }

  @Test
  public void testAvoidName() {
    // create f(x, y) and a loose variable z
    Type o = TypeFactory.createSort("o");
    Variable x = new Var("x", o);
    Variable y = new Var("y", o);
    Variable z = new Var("z", o);
    Constant f = new Constant("f", TypeFactory.createArrow(o, TypeFactory.createArrow(o, o)));
    Term term = f.apply(x).apply(y);

    NameGenerator generator = new NameGenerator(Set.of());
    MutableRenaming a = generator.generateUniqueNaming(term);
    generator.avoidAdditional(Set.of("x", "z"));
    MutableRenaming b = generator.generateUniqueNaming(term);

    assertFalse(a.isAvailable("x"));
    assertTrue(a.isAvailable("z"));
    assertFalse(b.isAvailable("x"));
    assertFalse(b.isAvailable("z"));
  }
}

