/**************************************************************************************************
 Copyright 2019--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.reader;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.parser.lib.ParsingException;
import charlie.trs.TRS;

public class ITrsInputReaderTest {
  @Test
  public void testReadTrsWithParsingErrors() {
    String str = "(VAR x y z) (RULES f(x y) -> g(z,x) g(x) -> f(z))";
    // no errors are given about the inconsistent arities, because we stop checking if there are
    // parser errors
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "1:24: Expected a comma or closing bracket but got IDENTIFIER (y).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testAbuseOfInfixSymbol() {
    String str = "(VAR x y) (RULES f(+(x,y)) -> 0)";
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "1:20: Expected an identifier (variable or function name) but got PLUS (+).\n" +
        "1:23: Expected closing bracket ')' but got COMMA (,).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testVariableUsedAsSymbol() {
    String str = "(VAR a g)\n" +
                 "(RULES g(a(x)) -> a(3))";
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "2:8: Variable g occurs with arguments like a function symbol.\n" +
        "2:10: Variable a occurs with arguments like a function symbol.\n" +
        "2:19: Variable a occurs with arguments like a function symbol.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testInconsistentArities() {
    String str = "(VAR x y z)\n" +
                 "(RULES f(x) -> g(x, x + f(x, z)) g(x,TRUE,z) -> h(y))";
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "2:25: Function symbol f occurs with 2 arguments, while it previously occurred with 1.\n" +
        "2:34: Function symbol g occurs with 3 arguments, while it previously occurred with 2.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadCorrectITrs() {
    String str =
      "# TRS/Beerendonk/10.trs\n" +
      "(VAR x)\n" +
      "(RULES\n" +
      "  eval(x) -> eval(x - 1) :|: x > 0 && !(x = 0) && (x % 2) > 0\n" +
      "  eval(x) -> eval(x / 2) :|: x > 0 && !(x = 0) && (x % 2) = 0\n" +
      ")\n";
    TRS trs = ITrsInputReader.readTrsFromString(str);
    assertTrue(trs.lookupSymbol("eval").queryType().toString().equals("Int → o"));
    assertTrue(trs.lookupSymbol("/") == null);
    assertTrue(trs.queryRuleCount() == 2);
    assertTrue(trs.queryRule(0).toString().equals(
      "eval(x) → eval(x - 1) | x > 0 ∧ ¬(x = 0) ∧ x % 2 > 0"));
    assertTrue(trs.queryRule(1).toString().equals(
      "eval(x) → eval(x / 2) | x > 0 ∧ ¬(x = 0) ∧ x % 2 = 0"));
  }

  @Test
  public void testCorrectTypeDerivation() {
    String str =
      "(VAR x y u v)\n" +
      "(RULES\n" +
      "  f(TRUE, x, y) -> fNat(x >= 0 && y >= 0, x, y)\n" +
      "  fNat(TRUE, x, y) -> f(x > y, x, round(y+1))\n" +
      "  round(x) -> if(x % 2 = 0, x, x+1)\n" +
      "  if(TRUE, u, v) -> u\n" +
      "  if(FALSE, u, v) -> v\n" +
      ")";
    TRS trs = ITrsInputReader.readTrsFromString(str);
    assertTrue(trs.lookupSymbol("f").queryType().toString().equals("Bool → Int → Int → o"));
    assertTrue(trs.lookupSymbol("fNat").queryType().toString().equals("Bool → Int → Int → o"));
    assertTrue(trs.lookupSymbol("round").queryType().toString().equals("Int → Int"));
    assertTrue(trs.lookupSymbol("if").queryType().toString().equals("Bool → Int → Int → Int"));
  }

  @Test
  public void testIncorrectTypeDerivation() {
    String str =
      "(VAR x y)\n" +
      "(RULES\n" +
      "  f(x) -> if(x > 0, x + 1, x - 1)\n" +
      "  negate(y) -> if(y, FALSE, TRUE)\n" +
      "  if(TRUE, x, y) -> x\n" +
      "  if(FALSE, x, y) -> y\n" +
      ")";
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals("I could not derive a valid typing " +
        "(Int and Bool positions are not consistentnly used).\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testDeriveConstraintVariableType() {
    String str =
      "(VAR x)\n" +
      "(RULES f(x) -> 5 :|: x)\n";
    TRS trs = ITrsInputReader.readTrsFromString(str);
    assertTrue(trs.lookupSymbol("f").queryType().toString().equals("Bool → Int"));
    assertTrue(trs.queryRuleCount() == 1);
    assertTrue(trs.queryRule(0).toString().equals("f(x) → 5 | x"));
  }

  @Test
  public void testIllegalVariableReduction() {
    String str =
      "(VAR x)\n" +
      "(RULES x -> a :|: x > 0)\n";
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "2:10: The left-hand side of a rule is not allowed to be a variable.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testVariableCreation() {
    // f(x) -> g(y, x)
    String str =
      "(VAR x y z)\n" +
      "(RULES f(x) -> g(y, x))\n";
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "2:13: Illegal rule [f(x) -> g(y, x)]: this rule may not occur in LCTRSs because the " +
          "right-hand side contains a variable that does not occur in the left-hand side or the " +
          "constraint.\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testVariableCreationWhenTypeIsDerivable() {
    // we still don't allow it here!
    String str =
      "(VAR x y z)\n" +
      "(RULES\n" +
      "  f(x) -> g(y, x)\n" +
      "  g(x, y) -> f(x + y)\n" +
      ")";
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals(
        "3:8: Illegal rule [f(x) -> g(y, x)]: this rule may not occur in LCTRSs because the " +
        "right-hand side contains a variable that does not occur in the left-hand side or the " +
        "constraint.\n"));
      return;
    }
  }

  @Test
  public void testIllegalLCTRS() {
    String str =
      "(VAR x y)\n" +
      "(RULES\n" +
      "  !(y) -> if(y, FALSE, TRUE)\n" +
      "  if(TRUE, x, y) -> x\n" +
      "  if(FALSE, x, y) -> y\n" +
      ")";
    try { ITrsInputReader.readTrsFromString(str); }
    catch (ParsingException e) {
      assertTrue(e.getMessage().equals("3:8: Illegal rule [¬y -> if(y, false, true)]: the " +
        "left-hand side is a theory term!\n"));
      return;
    }
    assertTrue(false);
  }
}

