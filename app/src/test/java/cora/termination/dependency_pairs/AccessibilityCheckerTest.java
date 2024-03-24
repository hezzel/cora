/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

// WARNING: MOST OF THE TESTS IN THIS FILE HAVE BEEN DISABLED
// This is because they use the SMT solver, and we don't want to do loads of file access in unit
// tests.  If you make changes to the file, please uncomment for a bit to check that it didn't
// muck anything up. :)

package cora.termination.dependency_pairs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import static org.junit.jupiter.api.Assertions.*;

import charlie.types.*;
import cora.terms.*;
import cora.trs.*;
import cora.reader.CoraInputReader;

class AccessibilityCheckerTest {
  private Type type(String text) {
    return CoraInputReader.readType(text);
  }

  /**
   * Enable this function to run all the tests on checkAccessibility (which uses the SMT solver),
   * disable it to only run the checks if the SMT problem is correct.
   */
  private void checkAccessible(AccessibilityChecker checker, boolean value) {
    //assertTrue(checker.checkAccessibility() == value);
  }

  @Test
  public void testObviouslyAccessibleFirstOrder() {
    TRS trs = CoraInputReader.readTrsFromString(
      "cons :: Int -> list -> list\n" +
        "nil :: list\n" +
        "append :: list -> list -> list\n" +
        "append(nil, z) -> z\n" +
        "append(cons(x,y), z) -> cons(x, append(y,z))\n");
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    // no requirement for z, but requirements for x and y
    assertTrue(checker.printTrsConstraints().equals("(>= i1 i2)\n(>= i1 i1)\n"));
    checkAccessible(checker, true);
    //System.out.println(checker.querySortOrdering());
  }

  @Test
  public void testPlainFunctionPassing() {
    TRS trs = CoraInputReader.readTrsFromString(
      "cons :: Int -> list -> list\n" +
        "nil :: list\n" +
        "map :: (Int -> Int) -> list -> list\n" +
        "map(F, nil) -> nil\n" +
        "map(F, cons(x,y)) -> cons(F(x), map(F, y))\n");
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    // same as append: we only care about the arguments of strict subterms, and that's cons(x,y)
    assertTrue(checker.printTrsConstraints().equals("(>= i1 i2)\n(>= i1 i1)\n"));
  }

  @Test
  public void testListFold() {
    TRS trs = CoraInputReader.readTrsFromString(
      "cons :: (A -> A) -> list -> list\n" +
        "nil :: list\n" +
        "lfold :: list -> A -> A\n" +
        "lfold(nil, x) -> x\n" +
        "lfold(cons(F,tl), x) -> lfold(tl, F(x))\n");
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    // list > A, list ≥ A (for F), list ≥ list (for tl)
    assertTrue(checker.printTrsConstraints().toString().equals(
      "(and (> i1 i2) (>= i1 i2))\n(>= i1 i1)\n"));
    checkAccessible(checker, true);
    //System.out.println(checker.querySortOrdering());
  }

  @Test
  public void testOrdrec() {
    TRS trs = CoraInputReader.readTrsFromString(
      "0 :: ord\n" +
        "s :: ord -> ord\n" +
        "lim :: (nat -> ord) -> ord\n" +
        "rec :: ord -> a -> (ord -> a -> a) -> ((nat -> ord) -> (nat -> a) -> a) -> a\n" +
        "helper :: (nat -> ord) -> a -> (ord -> a -> a) -> ((nat -> ord) -> (nat -> a) -> a) -> nat -> a\n" +
        "rec(0, z, F, G) -> z\n" +
        "rec(s(x), z, F, G) -> F(x, rec(x, z, F, G))\n" +
        "rec(lim(H), z, F, G) -> G(H, helper(H, z, F, G))\n" +
        "helper(H, z, F, G, n) -> rec(H(n), z, F, G)\n",
      TrsFactory.STRS
    );
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    // ord ≥ ord (for x), ord ≥ ord, ord > nat (for H)
    assertTrue(checker.printTrsConstraints().toString().equals(
      "(>= i1 i1)\n(and (> i1 i2) (>= i1 i1))\n"));
    checkAccessible(checker, true);
    //System.out.println(checker.querySortOrdering());
  }

  @Test
  public void testUntypedLambdaCalculus() {
    TRS trs = CoraInputReader.readTrsFromString(
      "app :: term -> term -> term\n" +
        "lam :: (term -> term) -> term\n" +
        "app(lam(F), X) -> F(X)\n");
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    // term > term (for the input type term) and term ≥ term (for the output type)
    assertTrue(checker.printTrsConstraints().toString().equals(
      "(and (> i1 i1) (>= i1 i1))\n"));
    checkAccessible(checker, false);
  }
}
