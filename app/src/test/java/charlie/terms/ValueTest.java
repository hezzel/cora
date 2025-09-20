/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

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

import java.util.ArrayList;
import java.util.TreeMap;
import java.util.TreeSet;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import charlie.types.TypeFactory;
import charlie.terms.position.*;

public class ValueTest extends TermTestFoundation {
  @Test
  public void testValueBasics() {
    Value v = new IntegerValue(-37);
    Value b = new BooleanValue(true);
    Value s = new StringValue("Hello\nworld");
    assertTrue(v.queryType().toString().equals("Int"));
    assertTrue(b.queryType().toString().equals("Bool"));
    assertTrue(s.queryType().toString().equals("String"));
    assertFalse(v.isVariable());
    assertTrue(b.isConstant());
    assertTrue(s.isFunctionalTerm());
    assertFalse(v.isVarTerm());
    assertFalse(b.isApplication());
    assertFalse(s.isAbstraction());
    assertFalse(v.isMetaApplication());
    assertFalse(b.isBetaRedex());
    assertTrue(s.isGround());
    assertTrue(v.isClosed());
    assertTrue(b.isTrueTerm());
    assertTrue(s.isTheoryTerm());
    assertTrue(v.isValue());
    assertTrue(b.numberArguments() == 0);
    assertTrue(s.numberMetaArguments() == 0);
    assertTrue(v.queryImmediateHeadSubterm(0) == v);
    assertTrue(b.queryHead() == b);
    assertTrue(s.queryRoot() == s);
    assertTrue(v.toValue() == v);
    assertTrue(b.isFirstOrder());
    assertTrue(s.isPattern());
    assertTrue(v.isApplicative());
    assertTrue(b.querySubterms().size() == 1);
    assertTrue(b.queryPositions(true).size() == 1);
    assertTrue(s.queryPositions(false).size() == 1);
    assertTrue(v.vars().size() == 0);
    assertTrue(b.mvars().size() == 0);
    assertTrue(s.freeReplaceables().size() == 0);
    assertTrue(b.boundVars().size() == 0);
    assertTrue(v.replaceSubterm(Position.empty, new IntegerValue(20)).toString().equals("20"));
    assertTrue(s.querySubterm(Position.empty) == s);
    assertTrue(v.toString().equals("-37"));
    assertTrue(b.toString().equals("true"));
    assertTrue(s.toString().equals("\"Hello\\nworld\""));
    assertTrue(b.renameAndRefreshBinders(new TreeMap<Variable,Variable>()) == b);
    assertTrue(v.apply(new ArrayList<Term>()) == v);
  }

  @Test
  public void testStore() {
    TreeSet<FunctionSymbol> set = new TreeSet<FunctionSymbol>();
    Value v = new StringValue("test");
    v.storeFunctionSymbols(set);
    assertTrue(set.size() == 1);
    assertTrue(set.contains(v));
  }

  @Test
  public void testValueApply() {
    Value v = new IntegerValue(13);
    assertThrows(TypingException.class, () -> v.apply(new Constant("a", baseType("o"))));
  }

  @Test
  public void testEquality() {
    Value n = new IntegerValue(42);
    Value b = new BooleanValue(false);
    Value s = new StringValue("test");
    assertTrue(n.equals(n));
    assertTrue(n.equals(new IntegerValue(42)));
    assertTrue(n.hashCode() == 42);
    assertFalse(n.equals(new IntegerValue(-42)));
    assertFalse(n.equals(b));
    assertTrue(b.equals(b));
    assertTrue(b.hashCode() == (new BooleanValue(false)).hashCode());
    assertTrue(b.hashCode() != (new BooleanValue(true)).hashCode());
    assertTrue(b.equals(new BooleanValue(false)));
    assertFalse(b.equals(new BooleanValue(true)));
    assertFalse(b.equals(s));
    FunctionSymbol f = new Constant("42", TypeFactory.intSort);
    Term bb = new Constant("false", TypeFactory.boolSort);
    Term ss = new Constant("\"test\"", TypeFactory.stringSort);
    assertFalse(n.equals(f));
    assertFalse(f.equals(n));
    assertFalse(b.equals(bb));
    assertFalse(bb.equals(b));
    assertFalse(s.equals(ss));
    assertFalse(ss.equals(s));
    assertTrue(s.hashCode() == (new StringValue("test")).hashCode());
    assertTrue(s.hashCode() != ss.hashCode());
  }

  @Test
  public void testEscapedString() throws IncorrectStringException {
    StringValue v = StringValue.parseUserStringValue("\"this\\\\is\\nokay\\\"!\"");
    assertTrue(v.toUniqueString().equals("\"this\\\\is\\nokay\\\"!\""));
    assertTrue(v.getString().equals("this\\is\nokay\"!"));
  }

  @Test
  public void testVariableRequest() {
    Term v = new IntegerValue(-12);
    assertThrows(InappropriatePatternDataException.class, () -> v.queryVariable());
  }

  @Test
  public void testAbstractionSubtermRequest() {
    Term v = new BooleanValue(true);
    assertThrows(InappropriatePatternDataException.class, () -> v.queryAbstractionSubterm());
  }

  @Test
  public void testArgumentPositionRequest() {
    Term v = new StringValue("333");
    assertThrows(InvalidPositionException.class, () ->
      v.querySubterm(new ArgumentPos(1, Position.empty)));
  }

  @Test
  public void testHeadPositionRequest() {
    Term v = new IntegerValue(31);
    assertThrows(InvalidPositionException.class, () -> v.querySubterm(new FinalPos(1)));
  }

  @Test
  public void testBadPositionReplacement() {
    Term v = new BooleanValue(true);
    assertThrows(InvalidPositionException.class, () ->
      v.replaceSubterm(new ArgumentPos(1, Position.empty), new Constant("a", baseType("a"))));
  }
}
