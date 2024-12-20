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
import charlie.util.Pair;
import charlie.parser.CoraParser;

/**
 * Not too many tests here, because most testing is actually done through the toString() functions
 * of the various kinds of terms.
 */
public class RenamingTest {
  private Renaming makeRenaming() {
    return new Renaming(Set.of("ban", "uu", "var"));
  }

  @Test
  public void testAddAndRemove() {
    Variable x = TermFactory.createVar("x", CoraParser.readType("a"));
    MetaVariable y = TermFactory.createMetaVar("z", CoraParser.readType("a -> b -> c"), 2);
    Renaming ren = makeRenaming();
    assertTrue(ren.setName(x, "x"));
    assertTrue(ren.setName(y, "y"));
    assertTrue(ren.getReplaceable("x") == x);
    assertTrue(ren.getReplaceable("y") == y);
    assertTrue(ren.getReplaceable("z") == null);
    assertTrue(ren.getName(x).equals("x"));
    assertTrue(ren.getName(y).equals("y"));
    ren.unsetName(x);
    assertTrue(ren.getName(x) == null);
    assertTrue(ren.getName(y).equals("y"));
    assertTrue(ren.getReplaceable("x") == null);
    assertTrue(ren.getReplaceable("y") == y);
    assertTrue(ren.isAvailable("x"));
    assertTrue(ren.setName(y, "x"));
    assertTrue(ren.domain().size() == 1);
    assertTrue(ren.range().size() == 1);
  }

  @Test
  public void testDomainAndRange() {
    Variable x = TermFactory.createVar("x", CoraParser.readType("a"));
    MetaVariable y = TermFactory.createMetaVar("z", CoraParser.readType("a -> b -> c"), 2);
    Renaming ren = makeRenaming();
    assertTrue(ren.setName(x, "x"));
    assertTrue(ren.setName(y, "y"));
    assertTrue(ren.domain().size() == 2);
    assertTrue(ren.range().size() == 2);
    assertTrue(ren.domain().contains(x));
    assertTrue(ren.domain().contains(y));
    assertTrue(ren.range().contains("x"));
    assertTrue(ren.range().contains("y"));
    assertFalse(ren.range().contains("z"));

    ren.unsetName(y);
    assertTrue(ren.domain().size() == 1);
    assertTrue(ren.range().size() == 1);
    assertTrue(ren.domain().contains(x));
    assertFalse(ren.domain().contains(y));
    assertTrue(ren.range().contains("x"));
    assertFalse(ren.range().contains("y"));
  }

  @Test
  public void testGetVariable() {
    Variable x = TermFactory.createVar("x", CoraParser.readType("a"));
    MetaVariable y = TermFactory.createMetaVar("x", CoraParser.readType("a -> b -> c"), 2);
    Renaming ren = makeRenaming();
    assertTrue(ren.setName(x, "x"));
    assertTrue(ren.setName(y, "y"));
    assertTrue(ren.getVariable("x") == x);
    assertTrue(ren.getVariable("y") == null);
  }

  @Test
  public void testLegalRename() {
    Variable x = TermFactory.createVar("x", CoraParser.readType("a"));
    Variable y = TermFactory.createVar("x", CoraParser.readType("a"));
    Renaming ren = makeRenaming();
    assertTrue(ren.setName(x, "x"));
    assertTrue(ren.setName(x, "y"));
    assertTrue(ren.getName(x).equals("y"));
    assertTrue(ren.getVariable("y") == x);
    assertTrue(ren.getVariable("x") == null);
    assertTrue(ren.isAvailable("x"));   // after renaming, x became available again
    assertFalse(ren.isAvailable("y"));
    assertTrue(ren.setName(y, "x"));
    assertTrue(ren.getVariable("x") == y);
    assertTrue(ren.setName(y, "x"));    // renaming to itself is allowed!
    assertTrue(ren.getVariable("x") == y);
    assertTrue(ren.getName(x).equals("y"));
    assertTrue(ren.getName(y).equals("x"));
  }

  @Test
  public void testIllegalName() {
    Variable x = TermFactory.createVar("x", CoraParser.readType("a"));
    MetaVariable y = TermFactory.createMetaVar("y", CoraParser.readType("a -> b -> c"), 2);
    Renaming ren = makeRenaming();
    assertTrue(ren.setName(x, "x"));
    assertFalse(ren.setName(y, "ban"));
    assertTrue(ren.getName(y) == null);
    assertTrue(ren.getReplaceable("ban") == null);
    assertTrue(ren.getReplaceable("y") == null);
    assertFalse(ren.setName(x, "ban"));
    assertTrue(ren.getName(x).equals("x"));
    assertTrue(ren.getReplaceable("x") == x);
    assertTrue(ren.getReplaceable("ban") == null);
  }

  @Test
  public void testDuplicateName() {
    Variable x = TermFactory.createVar("x", CoraParser.readType("b"));
    Variable y = TermFactory.createVar("y", CoraParser.readType("b"));
    Renaming ren = makeRenaming();
    assertTrue(ren.setName(x, "z"));
    assertFalse(ren.setName(y, "z"));
    assertTrue(ren.getReplaceable("z") == x);
    assertTrue(ren.getName(x).equals("z"));
    assertTrue(ren.getName(y) == null);

    assertTrue(ren.setName(y, "y"));
    assertFalse(ren.setName(y, "z")); // cannot rename to an already-used name either!
    assertTrue(ren.getReplaceable("z") == x);
    assertTrue(ren.getName(x).equals("z"));
    assertTrue(ren.getName(y).equals("y"));
    assertTrue(ren.getReplaceable("y") == y);
  }

  @Test
  public void testAddToAvoid() {
    Variable x = TermFactory.createVar("x", CoraParser.readType("b"));
    Renaming ren = makeRenaming();
    
    ren.avoid("x");
    assertFalse(ren.setName(x, "x"));
    assertTrue(ren.getName(x) == null);
    assertTrue(ren.getReplaceable("x") == null);
    assertFalse(ren.isAvailable("x"));

    assertTrue(ren.setName(x, "y"));
    ren.avoid("y");
    assertTrue(ren.getName(x).equals("y"));
    assertTrue(ren.getReplaceable("y") == x);
    assertFalse(ren.isAvailable("y"));

    assertTrue(ren.setName(x, "z"));
    assertTrue(ren.getName(x).equals("z"));
    assertTrue(ren.getReplaceable("z") == x);
    assertTrue(ren.getReplaceable("y") == null);
    assertFalse(ren.isAvailable("y"));
    assertFalse(ren.isAvailable("z"));
  }

  @Test
  public void testCopy() {
    Renaming renaming = makeRenaming();
    Variable x = TermFactory.createVar("x", CoraParser.readType("b"));
    Variable y = TermFactory.createVar("y", CoraParser.readType("b"));
    renaming.setName(x, "x");
    renaming.setName(y, "q");
    Renaming ren2 = renaming.copy();
    renaming.setName(y, "y");
    Variable z1 = TermFactory.createVar("z1", CoraParser.readType("a"));
    Variable z2 = TermFactory.createVar("z2", CoraParser.readType("b"));
    renaming.setName(z1, "z");
    ren2.setName(z2, "z");
    renaming.avoid("a");
    ren2.avoid("b");

    assertTrue(renaming.getName(x).equals("x"));
    assertTrue(renaming.getName(y).equals("y"));
    assertTrue(renaming.getName(z1).equals("z"));
    assertTrue(renaming.getName(z2) == null);
    assertTrue(renaming.getReplaceable("x") == x);
    assertTrue(renaming.getReplaceable("y") == y);
    assertTrue(renaming.getReplaceable("z") == z1);
    assertTrue(renaming.getReplaceable("q") == null);
    assertFalse(renaming.isAvailable("a"));
    assertTrue(renaming.isAvailable("b"));

    assertTrue(ren2.getName(x).equals("x"));
    assertTrue(ren2.getName(y).equals("q"));
    assertTrue(ren2.getName(z1) == null);
    assertTrue(ren2.getName(z2).equals("z"));
    assertTrue(ren2.getReplaceable("x") == x);
    assertTrue(ren2.getReplaceable("y") == null);
    assertTrue(ren2.getReplaceable("z") == z2);
    assertTrue(ren2.getReplaceable("q") == y);
    assertTrue(ren2.isAvailable("a"));
    assertFalse(ren2.isAvailable("b"));
  }

  @Test
  public void testLimit() {
    Renaming renaming = makeRenaming();
    Variable x = TermFactory.createVar("x", CoraParser.readType("b"));
    Variable y = TermFactory.createVar("y", CoraParser.readType("b"));
    Variable z = TermFactory.createVar("z", CoraParser.readType("b"));
    Variable w = TermFactory.createVar("w", CoraParser.readType("b"));
    renaming.setName(x, "x");
    renaming.setName(y, "q");

    FunctionSymbol f = TermFactory.createConstant("f", CoraParser.readType("b -> b"));
    FunctionSymbol g = TermFactory.createConstant("g", CoraParser.readType("b -> b -> b"));
    Term a = f.apply(x);          // f(x)
    Term b = g.apply(x).apply(z); // g(x, z)
    Term c = g.apply(w).apply(z); // g(w, z)

    renaming.limitDomain(a, b, c);

    assertTrue(renaming.domain().size() == 1);
    assertTrue(renaming.getName(x).equals("x"));
    assertTrue(renaming.getReplaceable("y") == null);
  }
}

