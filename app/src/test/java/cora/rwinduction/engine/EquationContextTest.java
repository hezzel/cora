/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

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

import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.terms.Variable;
import charlie.trs.TRS;
import charlie.reader.CoraInputReader;
import cora.io.OutputModule;

class EquationContextTest {
  @Test
  public void testToStringEmptyExtra() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum2 :: Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("sum1(x)", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("sum2(x + y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Equation equation = new Equation(left, right, constraint);
    EquationContext context = new EquationContext(equation, 7, renaming);
    assertTrue(context.toString().equals("E7: (• , sum1(x) ≈ sum2(x + y) | x > 0 ∧ y = 0 , •)"));
  }

  @Test
  public void testToStringWithExtra() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum2 :: Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("sum1(x)", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("sum2(x + y)", renaming, trs);
    Term eright = CoraInputReader.readTermAndUpdateNaming("sum2(y + 1)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Equation equation = new Equation(left, right, constraint);
    EquationContext context = new EquationContext(left, equation, eright, 13, renaming);
    assertTrue(context.toString().equals(
      "E13: (sum1(x) , sum1(x) ≈ sum2(x + y) | x > 0 ∧ y = 0 , sum2(y + 1))"));
  }

  @Test
  public void testRenamingInConstructor() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum2 :: Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("sum1(x)", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("sum2(x + y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Term kk = CoraInputReader.readTermAndUpdateNaming("sum1(z)", renaming, trs);
    Equation eq = new Equation(left, right, constraint);
    EquationContext context = new EquationContext(eq, 8, renaming);
    assertTrue(context.getRenaming().getReplaceable("z") == null);
    assertTrue(renaming.getReplaceable("z") != null);
    assertThrows(IllegalArgumentException.class, () -> new EquationContext(left, eq, kk,
      7, context.getRenaming()));
    Equation badeq = new Equation(kk, right);
    assertThrows(IllegalArgumentException.class, () -> new EquationContext(badeq, 10,
      context.getRenaming()));
  }

  @Test
  public void testModifyingRenamingDoesNotMatter() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum2 :: Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("sum1(x)", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("sum2(x + y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Term kk = CoraInputReader.readTermAndUpdateNaming("sum1(z)", renaming, trs);
    Equation eq = new Equation(left, right, constraint);
    EquationContext context = new EquationContext(eq, 8, renaming);
    Variable x = renaming.getVariable("x");
    context.getRenaming().setName(x, "AAA");
    assertTrue(renaming.getName(x).equals("x"));
  }

  @Test
  public void testIndex() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "sum1 :: Int -> Int\n" +
      "sum2 :: Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("sum1(x)", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("sum2(x + y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Equation eq = new Equation(left, right, constraint);
    EquationContext context = new EquationContext(left, eq, right, 8, renaming);
    assertTrue(context.getIndex() == 8);
    assertTrue(context.getName().equals("E8"));
    assertThrows(IllegalArgumentException.class, () ->
      new EquationContext(left, eq, right, 0, renaming));
    assertThrows(IllegalArgumentException.class, () ->
      new EquationContext(eq, -1, renaming));
  }

  @Test
  public void testPrintableObject() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "h :: Int -> o\n" +
      "g :: Int -> Int -> Int\n");
    Term left = CoraInputReader.readTermAndUpdateNaming("f(f(x))", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("g(x,y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ y = 0", renaming, trs);
    Equation equation = new Equation(left, right, constraint);
    renaming.setName(renaming.getVariable("x"), "z");
    EquationContext context = new EquationContext(left, equation, right, 103, renaming);
    OutputModule module = OutputModule.createUnicodeModule(trs);
    module.println("%a", context);
    assertTrue(module.toString().equals(
      "E103: (f(f(z)) , f(f(z)) ≈ g(z, y) | z > 0 ∧ y = 0 , g(z, y))\n\n"));
  }

  @Test
  public void testReplace() {
    Renaming renaming = new Renaming(Set.of());
    TRS trs = CoraInputReader.readTrsFromString(
      "f :: Int -> Int\n" +
      "h :: Int -> o\n" +
      "g :: Int -> Int -> Int\n");
    
    Term left = CoraInputReader.readTermAndUpdateNaming("f(f(x))", renaming, trs);
    Term right = CoraInputReader.readTermAndUpdateNaming("g(x,y)", renaming, trs);
    Term constraint = CoraInputReader.readTermAndUpdateNaming("x > 0 ∧ z = 0", renaming, trs);
    Term extra = CoraInputReader.readTerm("f(z)", renaming, trs);
    Equation equation1 = new Equation(left, right, constraint);
    EquationContext c1 = new EquationContext(left, equation1, extra, 103, renaming);

    Term constraint2 = CoraInputReader.readTerm("x > 0", renaming, trs);
    Equation equation2 = new Equation(left, left, constraint2);
    EquationContext c2 = c1.replace(equation2, 107);

    assertTrue(c2.toString().equals("E107: (f(f(x)) , f(f(x)) ≈ f(f(x)) | x > 0 , f(z))"));
    assertTrue(c2.getRenaming().getReplaceable("y") == null);
    assertTrue(c1.getRenaming().getReplaceable("y") != null);
  }
}

