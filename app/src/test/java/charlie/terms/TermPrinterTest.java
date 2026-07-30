/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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

/**
 * Not too many tests here, because most testing is actually done through the toString() functions
 * of the various kinds of terms.
 */
public class TermPrinterTest {
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
    TermPrinter printer = new TermPrinter(generator);
    MutableRenaming naming = generator.generateUniqueNaming(term, x);
    StringBuilder builder = new StringBuilder();
    printer.print(term, naming, builder);
    assertTrue(naming.getName(x).equals("x"));
    assertTrue(naming.getName(y) == null);
    assertFalse(naming.isAvailable("x"));
    assertTrue(naming.isAvailable("y"));
    assertTrue(builder.toString().equals("f(λx.x, λy.y)"));
    naming = new MutableRenaming(Set.of("y"));
    naming.setName(x, "z");
    assertTrue(printer.print(term, naming).equals("f(λz.z, λy.y)"));
      // the name generator tells us what variable names to avoid, NOT the names blocked in the
      // free renaming!
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
    TermPrinter printer = new TermPrinter(generator);
    assertTrue(printer.print(abs).equals("λx.λy.λx__1.f(g(z__2, x__1), z__1, x)"));

    MutableRenaming naming = new MutableRenaming(Set.of());
    assertEquals("λx.λy.λx__1.f(g(z, x__1), z, x)", printer.print(abs, naming));

    naming = generator.generateUniqueNaming(new Var("x", o));
    assertEquals("λx__1.λy.λx__2.f(g(z, x__2), z, x__1)", printer.print(abs, naming));
  }
}

