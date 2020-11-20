/**************************************************************************************************
 Copyright 2020 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import java.util.TreeMap;
import java.util.HashSet;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;

/**
 * This class tests the pretty printing functionality for terms that prevents distinct variables
 * with the same name from being displayed the same.
 */
public class TermPrettyPrintTest extends TermTestInherit {
  /**
   * Given a string that represents a term, and a pattern that may contain codes %i in place of
   * some variables, this returns null if original is not an instance of the pattern (where only
   * the codes may be instantiated), and otherwise returns the mapping from codes variable names.
   */
  private TreeMap<String,String> match(String original, String pattern) {
    TreeMap<String,String> ret = new TreeMap<String,String>();
    int i = 0, j = 0;
    System.out.println("Matching " + original + " against " + pattern);
    while (i < pattern.length()) {
      System.out.println("i = " + i + "; j = " + j);
      if (j >= original.length()) return null;
      if (pattern.charAt(i) == '%') {
        // read the full code
        int k = i + 1;
        while (k < pattern.length() && pattern.charAt(k) >= '0' && pattern.charAt(k) <= '9') k++;
        String code = pattern.substring(i, k);
        i = k;
        // read the variable
        k = j + 1;
        while (k < original.length() && original.charAt(k) != ' ' && original.charAt(k) != ')' &&
               original.charAt(k) != '(' && original.charAt(k) != ',' &&
               original.charAt(k) != '.') k++;
        String varname = original.substring(j, k);
        j = k;
        // does this conflict with an existing mapping?
        if (ret.containsKey(code) && !ret.get(code).equals(varname)) return null;
        // if not, just store the mapping code => varname
        ret.put(code, varname);
      }
      else {
        if (pattern.charAt(i) != original.charAt(j)) return null;
        else { i++; j++; }
      }
    }
    return ret;
  }

  /**
   * This tests whether original is an instance of pattern (as described in the match function),
   * and each distinct code is instantiated by a different variable name.
   */
  private boolean checkDistinctMatch(String original, String pattern) {
    TreeMap<String,String> map = match(original, pattern);
    if (map == null) return false;
    return map.values().size() == (new HashSet(map.values())).size();
  }

  @Test
  public void testDifferentVariablesIrrelevant() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = binderVariable("x", baseType("o"));
    Abstraction abs1 = new Abstraction(x, x);
    Abstraction abs2 = new Abstraction(y, y);
    Alphabet alf = new UserDefinedAlphabet(new ArrayList<FunctionSymbol>());
    assertTrue(abs1.toPrettyString(alf).equals(abs2.toPrettyString(alf)));
  }

  @Test
  public void testPrintDuplicateAbstractions() {
    Type o = baseType("o");
    Type oo = arrowType("o", "o");
    Type ooooo = new ArrowType(oo, new ArrowType(oo, o));
    Variable x = new BinderVariable("x", o);
    FunctionSymbol f = new Constant("f", ooooo);
    Abstraction abs = new Abstraction(x, x);
    Term combi = new FunctionalTerm(f, abs, abs);
    Alphabet alf = new UserDefinedAlphabet(new ArrayList<FunctionSymbol>());
    assertTrue(combi.toPrettyString(alf).equals("f(λx.x, λx.x)"));
  }

  @Test
  public void testRenamingWithBoundVariables() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = binderVariable("x", baseType("o"));
    Term combi = binaryTerm("f", baseType("o"), y, x);
    Term abs1 = new Abstraction(x, combi);
    Term abs2 = new Abstraction(y, abs1);
    Alphabet alf = new UserDefinedAlphabet(new ArrayList<FunctionSymbol>());

    assertTrue(checkDistinctMatch(combi.toPrettyString(alf), "f(%1, %2)"));
    assertTrue(checkDistinctMatch(abs1.toPrettyString(alf), "λ%1.f(%2, %1)"));
    assertTrue(checkDistinctMatch(abs2.toPrettyString(alf), "λ%2.λ%1.f(%2, %1)"));
  }

  @Test
  public void testRenamingWithFreeVariables() {
    Variable x = freeVariable("x", baseType("o"));
    Variable y = freeVariable("x", baseType("o"));
    Variable z = binderVariable("x", baseType("o"));
    Term fyz = binaryTerm("f", baseType("o"), y, z);
    Term fxfyz = binaryTerm("f", baseType("o"), x, fyz);

    Alphabet alf = new UserDefinedAlphabet(new ArrayList<FunctionSymbol>());

    assertTrue(checkDistinctMatch(fxfyz.toPrettyString(alf), "f(%1, f(%2, %3))"));
  }

  @Test
  public void testRenamingWithNonLinearVariableOccurrence() {
    Variable x = freeVariable("x", baseType("o"));
    Variable y = freeVariable("x", baseType("o"));
    Variable z = binderVariable("x", baseType("o"));
    Term fxy = binaryTerm("f", baseType("o"), x, y);
    Term fyz = binaryTerm("f", baseType("o"), y, z);
    Term ffxyfyz = binaryTerm("f", baseType("o"), fxy, fyz);

    Alphabet alf = new UserDefinedAlphabet(new ArrayList<FunctionSymbol>());

    assertFalse(checkDistinctMatch(ffxyfyz.toPrettyString(alf), "f(f(%1, %4), f(%2, %3))"));
    assertTrue(checkDistinctMatch(ffxyfyz.toPrettyString(alf), "f(f(%1, %2), f(%2, %3))"));
  }
}

