/**************************************************************************************************
 Copyright 2025 Cynthia Kop & Liye Guo

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.unification;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.terms.Renaming;
import charlie.reader.CoraInputReader;
import java.util.Set;

class MguFinderTest {
  @Test
  public void testTypeMismatch() {
    var renaming = new Renaming(Set.of());
    var trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "g :: o -> Int\n");

    var fx = CoraInputReader.readTermAndUpdateNaming("f(x)", renaming, trs);
    var f = CoraInputReader.readTermAndUpdateNaming("f", renaming, trs);
    var x = CoraInputReader.readTermAndUpdateNaming("x", renaming, trs);
    assertNull(MguFinder.mgu(f, x));

    var gy = CoraInputReader.readTermAndUpdateNaming("g(y)", renaming, trs);
    assertNull(MguFinder.mgu(fx, gy));
  }

  @Test
  public void testOccurrence() {
    var renaming = new Renaming(Set.of());
    var trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n");

    var fx = CoraInputReader.readTermAndUpdateNaming("f(x)", renaming, trs);
    var x = CoraInputReader.readTermAndUpdateNaming("x", renaming, trs);
    assertNull(MguFinder.mgu(x, fx));
  }

  @Test
  public void testVariable() {
    var renaming = new Renaming(Set.of());
    var trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n");

    CoraInputReader.readTermAndUpdateNaming("f(x)", renaming, trs);
    var x1 = CoraInputReader.readTermAndUpdateNaming("x", renaming, trs);
    var x2 = CoraInputReader.readTermAndUpdateNaming("x", renaming, trs);
    assertTrue(MguFinder.mgu(x1, x2).domain().isEmpty());

    CoraInputReader.readTermAndUpdateNaming("f(y)", renaming, trs);
    var y = CoraInputReader.readTermAndUpdateNaming("y", renaming, trs);
    var sub = MguFinder.mgu(x1, y);
    assertEquals(sub.domain().size(), 1);
    assertEquals(x1.substitute(sub), y.substitute(sub));
  }

  @Test
  public void testConstant() {
    var renaming = new Renaming(Set.of());
    var trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "g :: Int -> Int\n");

    var f1 = CoraInputReader.readTermAndUpdateNaming("f", renaming, trs);
    var f2 = CoraInputReader.readTermAndUpdateNaming("f", renaming, trs);
    assertTrue(MguFinder.mgu(f1, f2).domain().isEmpty());

    var g = CoraInputReader.readTermAndUpdateNaming("g", renaming, trs);
    assertNull(MguFinder.mgu(f1, g));
  }

  @Test
  public void testApplication1() {
    var renaming = new Renaming(Set.of());
    var trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int -> Int\n" +
      "a :: Int\n");

    var fxa = CoraInputReader.readTermAndUpdateNaming("f(x, a)", renaming, trs);
    var fay = CoraInputReader.readTermAndUpdateNaming("f(a, y)", renaming, trs);
    var sub = MguFinder.mgu(fxa, fay);
    assertEquals(sub.domain().size(), 2);

    var x = CoraInputReader.readTermAndUpdateNaming("x", renaming, trs);
    var y = CoraInputReader.readTermAndUpdateNaming("y", renaming, trs);
    var a = CoraInputReader.readTermAndUpdateNaming("a", renaming, trs);
    assertEquals(x.substitute(sub), a);
    assertEquals(y.substitute(sub), a);
  }

  @Test
  public void testApplication2() {
    var renaming = new Renaming(Set.of());
    var trs = CoraInputReader.readTrsFromString(
      "f :: o -> o\n" +
      "g :: o -> o -> o -> o\n" +
      "h :: (o -> o -> o) -> o\n" +
      "a :: o\n" +
      "b :: o\n");

    CoraInputReader.readTermAndUpdateNaming("h(F)", renaming, trs);
    var Fxfa = CoraInputReader.readTermAndUpdateNaming("F(x, f(a))", renaming, trs);
    var gaby = CoraInputReader.readTermAndUpdateNaming("g(a, b, y)", renaming, trs);
    var sub = MguFinder.mgu(Fxfa, gaby);
    assertEquals(sub.domain().size(), 3);

    var F = CoraInputReader.readTermAndUpdateNaming("F", renaming, trs);
    var ga = CoraInputReader.readTermAndUpdateNaming("g(a)", renaming, trs);
    var x = CoraInputReader.readTermAndUpdateNaming("x", renaming, trs);
    var b = CoraInputReader.readTermAndUpdateNaming("b", renaming, trs);
    var y = CoraInputReader.readTermAndUpdateNaming("y", renaming, trs);
    var fa = CoraInputReader.readTermAndUpdateNaming("f(a)", renaming, trs);
    assertEquals(F.substitute(sub), ga);
    assertEquals(x.substitute(sub), b);
    assertEquals(y.substitute(sub), fa);
  }

  @Test
  public void testApplication3() {
    var renaming = new Renaming(Set.of());
    var trs = CoraInputReader.readTrsFromString(
      "f :: o -> o -> o\n" +
      "g :: o -> o\n");

    var fxz = CoraInputReader.readTermAndUpdateNaming("f(x, z)", renaming, trs);
    var fygx = CoraInputReader.readTermAndUpdateNaming("f(y, g(x))", renaming, trs);
    var sub = MguFinder.mgu(fxz, fygx);
    assertEquals(sub.domain().size(), 2);
    assertEquals(fxz.substitute(sub), fygx.substitute(sub));

    var z = CoraInputReader.readTermAndUpdateNaming("z", renaming, trs);
    var g = CoraInputReader.readTermAndUpdateNaming("g", renaming, trs);
    assertEquals(z.substitute(sub).queryHead(), g);
    assertEquals(z.substitute(sub).numberArguments(), 1);
    assertTrue(z.substitute(sub).queryArgument(1).isVariable());
  }

  @Test
  public void testApplication4() {
    var renaming = new Renaming(Set.of());
    var trs = CoraInputReader.readTrsFromString(
      "f :: o -> o -> o\n" +
      "a :: o\n" +
      "b :: o\n");

    var fxb = CoraInputReader.readTermAndUpdateNaming("f(x, b)", renaming, trs);
    var fax = CoraInputReader.readTermAndUpdateNaming("f(a, x)", renaming, trs);
    assertNull(MguFinder.mgu(fxb, fax));
  }
}