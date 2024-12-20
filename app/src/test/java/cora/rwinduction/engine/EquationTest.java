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

package cora.rwinduction.engine;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;

import charlie.exceptions.CustomParserException;
import charlie.exceptions.TypingException;
import charlie.terms.position.Position;
import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;

class EquationTest {
  @Test
  public void testToString() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum2 :: Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("sum1(x)", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("sum2(x + y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Equation equation = new Equation(left, right, constraint, renaming);
    assertTrue(equation.toString().equals("sum1(x) ≈ sum2(x + y) | x > 0 ∧ y = 0"));
  }

  @Test
  public void testRenaming() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum2 :: Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("sum1(x)", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("sum2(x + y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Term kk = CoraInputReader.readTermAndUpdateNaming("sum1(z)", renaming, trs);
    Equation equation = new Equation(left, right, constraint, renaming);
    assertTrue(equation.getRenaming().getReplaceable("z") == null);
    assertTrue(renaming.getReplaceable("z") != null);
    assertThrows(IllegalArgumentException.class, () -> new Equation(kk, right, constraint,
      equation.getRenaming()));
  }

  @Test
  public void testReplaceGood() throws CustomParserException {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "g :: Int -> Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("f(f(x))", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("g(x,y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Equation equation = new Equation(left, right, constraint, renaming);
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    Term replacement = CoraInputReader.readTerm("g(3,y)", renaming, trs);
    Equation eq2 = equation.replaceSubterm(pos, replacement);
    assertTrue(eq2.toString().equals("f(g(3, y)) ≈ g(x, y) | x > 0 ∧ y = 0"));
  }

  @Test
  public void testReplaceBadType() throws CustomParserException {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "h :: Int -> o\n" +
      "g :: Int -> Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("f(f(x))", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("g(x,y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Equation equation = new Equation(left, right, constraint, renaming);
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    Term replacement = CoraInputReader.readTerm("h(3)", renaming, trs);
    assertThrows(TypingException.class, () -> equation.replaceSubterm(pos, replacement));
  }

  @Test
  public void testReplaceBadRenaming() throws CustomParserException {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "g :: Int -> Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("f(f(x))", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("g(x,y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Equation equation = new Equation(left, right, constraint, renaming);
    EquationPosition pos = new EquationPosition(EquationPosition.Side.Left, Position.parse("1"));
    Term replacement = CoraInputReader.readTermAndUpdateNaming("f(z)", renaming, trs);
    assertThrows(IllegalArgumentException.class, () -> equation.replaceSubterm(pos, replacement));
  }
}

