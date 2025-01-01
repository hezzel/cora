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

package cora.rwinduction.parser;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.Set;

import charlie.exceptions.ParseException;
import charlie.util.FixedList;
import charlie.terms.*;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.rwinduction.engine.Equation;

class SubstitutionParserTest {
  TRS trs = CoraInputReader.readTrsFromString (
    "sum :: Int -> Int\n" +
    "sum(x) -> 0         | x ≤ 0\n" +
    "sum(x) -> x + sum(x - 1) | x > 0"
  );

  @Test
  public void testParseSubstitution() {
    Variable x = TermFactory.createVar(CoraInputReader.readType("Int"));
    Variable z = TermFactory.createVar(CoraInputReader.readType("Int"));
    Renaming keys = new Renaming(Set.of());
    keys.setName(x, "x");
    keys.setName(z, "z");
    Renaming values = new Renaming(Set.of());
    Term t1 = CoraInputReader.readTermAndUpdateNaming("x + sum(y)", values, trs);
    Term t2 = CoraInputReader.readTermAndUpdateNaming("sum(3)", values, trs);
    Substitution subst =
      SubstitutionParser.parseSubstitution("[x := x + sum(y), z := sum(3)]", trs, keys, values);
    assertTrue(subst.get(x).equals(t1));
    assertTrue(subst.get(z).equals(t2));
  }

  @Test
  public void testMissingKey() {
    Renaming keys = new Renaming(Set.of());
    keys.setName(TermFactory.createVar("z", CoraInputReader.readType("Int")), "z");
    Renaming values = new Renaming(Set.of());
    Term t1 = CoraInputReader.readTermAndUpdateNaming("x + sum(y)", values, trs);
    assertThrows(ParseException.class, () ->
      SubstitutionParser.parseSubstitution("[x := x + sum(y), z := sum(3)]", trs, keys, values));
  }

  @Test
  public void testMissingVariableInValue() {
    Variable x = TermFactory.createVar(CoraInputReader.readType("Int"));
    Variable z = TermFactory.createVar(CoraInputReader.readType("Int"));
    Renaming keys = new Renaming(Set.of());
    keys.setName(x, "x");
    keys.setName(z, "z");
    Renaming values = new Renaming(Set.of());
    Substitution subst =
      SubstitutionParser.parseSubstitution("[x := x + sum(y), z := sum(3)]", trs, keys, values);
    assertTrue(subst.get(x).toString().equals("x + sum(y)"));
    assertTrue(subst.get(z).toString().equals("sum(3)"));
    assertTrue(values.getReplaceable("x") != null);
    assertTrue(values.getReplaceable("y") != null);
    assertTrue(values.getReplaceable("z") == null);
  }

  @Test
  public void testIllTypedSubstitution() {
    Variable z = TermFactory.createVar(CoraInputReader.readType("Bool"));
    Renaming keys = new Renaming(Set.of());
    keys.setName(z, "z");
    Renaming values = new Renaming(Set.of());
    assertThrows(ParseException.class, () ->
      SubstitutionParser.parseSubstitution("[z := sum(3)]", trs, keys, values));
  }
}
