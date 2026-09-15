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
import java.util.List;
import java.util.Set;
import charlie.types.*;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;

public class NameGeneratorTest {
  @Test
  public void testOriginallyBlockedNamesAreBlocked() {
    NameGenerator generator = new NameGenerator(Set.of("x"));
    Variable x = new Var("x", TypeFactory.defaultSort);
    Renaming renaming = generator.generateUniqueNaming(x);
    assertTrue(renaming.getName(x).equals("x__1"));
  }

  @Test
  public void testNamesBlockedLaterAreBlockedButOnlyInFutureRenamings() {
    Type o = TypeFactory.defaultSort;
    NameGenerator generator = new NameGenerator(Set.of());
    Variable x = new Var("x", o);
    Variable f = new Var("f", TypeFactory.createArrow(o, o));
    generator.avoidAdditional("f");
    // check that f is indeed blocked (and x is not)
    MutableRenaming renaming = generator.generateUniqueNaming(f.apply(x));
    assertTrue(renaming.getName(x).equals("x"));
    assertTrue(renaming.getName(f).equals("f__1"));
    generator.avoidAdditional(Set.of("y", "x"));
    // check that y is *not* blocked in the renaming generated before the change
    assertTrue(renaming.isAvailable("y"));
    renaming = generator.generateUniqueNaming(f.apply(x));
    // check that the new renaming does block what we expect, thus testing both ways of
    // using avoidAdditional
    assertTrue(renaming.getName(x).equals("x__1"));
    assertTrue(renaming.getName(f).equals("f__1"));
    assertFalse(renaming.isAvailable("y"));
  }

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
    MutableRenaming naming = generator.generateUniqueNaming(x1, x2, x3, x4, y, z1, z2);
    assertTrue(naming.getName(x1).equals("x__2"));
    assertTrue(naming.getName(x2).equals("x__3"));
    assertTrue(naming.getName(x3).equals("x__4"));
    assertTrue(naming.getName(mvar).equals("x__1"));  // meta-variables come before variables
    assertTrue(naming.getName(y).equals("y"));
    assertTrue(naming.getName(z1).equals("z__2"));  // binders come after non-binders
    assertTrue(naming.getName(z2).equals("z__1"));
    assertFalse(naming.isAvailable("x"));
    assertFalse(naming.isAvailable("z"));
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
    MutableRenaming naming =
      generator.generateUniqueNaming(x, y1, y2, z, u1, u2, v, w, a, b1, b2, b3);
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
    generator.extend(naming, List.of(v));
    assertTrue(naming.getName(v).equals("v"));
  }

  @Test
  public void testIllegalName() {
    NameGenerator generator = new NameGenerator(Set.of("_@"));
    Variable at = new Var("@", TypeFactory.defaultSort);
    Variable times = new Var("*", TypeFactory.defaultSort);
    Variable three = new Var("3", TypeFactory.defaultSort);
    Variable underthree = new Var("_3", TypeFactory.defaultSort);
    Variable foura = new Var("4", TypeFactory.defaultSort);
    Variable fourb = new Var("4", TypeFactory.defaultSort);
    Renaming naming = generator.generateUniqueNaming(at, times, three, underthree, foura, fourb);
    assertTrue(naming.getName(at).equals("_@__1"));
    assertTrue(naming.getName(times).equals("_*"));
    assertTrue(naming.getName(three).equals("_3__1"));
    assertTrue(naming.getName(underthree).equals("_3"));
    assertTrue(naming.getName(foura).equals("_4__1"));
    assertTrue(naming.getName(fourb).equals("_4__2"));
  }

  @Test
  public void testExtendWithExistingElement() {
    NameGenerator generator = new NameGenerator(Set.of());
    MutableRenaming naming = new MutableRenaming(Set.of());
    Variable x = new Var("x", TypeFactory.defaultSort);
    generator.extend(naming, List.of(x));
    assertTrue(naming.domain().size() == 1);
    generator.extend(naming, List.of(x));
    assertTrue(naming.domain().size() == 1);
  }

  @Test
  public void testExtendWithPartiallyNewTerm() {
    Type o = TypeFactory.defaultSort;
    NameGenerator generator = new NameGenerator(Set.of("y"));
    MutableRenaming naming = new MutableRenaming(Set.of("y"));
    Variable x = new Var("x", o);
    Variable x1 = new Var("x", o);
    Variable y = new Var("y", o);
    Variable z = new Var("z", o);
    naming.setName(x, "x");
    assertTrue(naming.domain().size() == 1);
    Term f = new Constant("f", TypeFactory.createArrow(o, TypeFactory.createArrow(o, o)));
    Term t = new Application(f, new Application(f, x, x1), new Application(f, y, z));
    generator.extend(naming, List.of(t));
    assertTrue(naming.domain().size() == 4);
    assertTrue(naming.getName(x).equals("x"));
    assertTrue(naming.getName(x1).equals("x__1"));
    assertTrue(naming.getName(y).equals("y__1"));
    assertTrue(naming.getName(z).equals("z"));
  }

  @Test
  public void testExtendWithIllegalName() {
    NameGenerator generator = new NameGenerator(Set.of());
    MutableRenaming naming = new MutableRenaming(Set.of());
    Type o = TypeFactory.defaultSort;
    Variable x = new Var("17", o);
    Variable y = new Var("_@", o);
    Variable a = new Var("17", o);
    Variable b = new Var("@", o);
    Variable c = new Var("", o);
    naming.setName(x, "17");
    naming.setName(y, "_@");
    generator.extend(naming, List.of(a, b, c));
    assertTrue(naming.domain().size() == 5);
    assertTrue(naming.getName(x).equals("17"));
    assertTrue(naming.getName(y).equals("_@"));
    assertTrue(naming.getName(a).equals("_17__1"));
    assertTrue(naming.getName(b).equals("_@__1"));
    assertTrue(naming.getName(c).equals("VAR"));
  }

  @Test
  public void testGenerateNameForSameBinderTwice() {
    NameGenerator generator = new NameGenerator(Set.of());
    Variable x = new Binder("x", TypeFactory.defaultSort);
    MutableRenaming naming = new MutableRenaming(Set.of());
    assertTrue(generator.generateBoundName(naming, x) != null);
    assertTrue(generator.generateBoundName(naming, x) == null);
  }

  @Test
  public void testGenerateNameForDifferentBindersWithSameName() {
    NameGenerator generator = new NameGenerator(Set.of());
    Variable x = new Binder("x", TypeFactory.defaultSort);
    Variable y = new Binder("x", TypeFactory.defaultSort);
    MutableRenaming naming = new MutableRenaming(Set.of());
    assertTrue(generator.generateBoundName(naming, x).equals("x"));
    assertTrue(generator.generateBoundName(naming, y).equals("x__1"));
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
    Variable z = new Binder("y", o);
    generator.generateBoundName(naming, z);
    assertTrue(naming.getName(y).equals("y"));
    assertTrue(naming.getName(z).equals("y__1"));
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
  public void testOverlapWithBanned() {
    Variable x = new Var("17", TypeFactory.createSort("a"));
    Variable y = new Var("_17", TypeFactory.createSort("a"));
    NameGenerator generator = new NameGenerator(Set.of());
    MutableRenaming a = generator.generateUniqueNaming(x, y);
    assertTrue(a.getName(y).equals("_17"));
    assertTrue(a.getName(x).equals("_17__1"));
  }
}
