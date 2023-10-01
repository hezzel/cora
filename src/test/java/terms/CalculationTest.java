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

package cora.terms;

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.ArrayList;
import cora.exceptions.*;
import cora.types.TypeFactory;
import cora.types.Type;

public class CalculationTest extends TermTestFoundation {
  @Test
  public void testBasics() {
    CalculationSymbol p = new PlusSymbol();
    CalculationSymbol t = new TimesSymbol();
    CalculationSymbol a = new AndOrSymbol(false);
    CalculationSymbol o = new AndOrSymbol(true);
    assertFalse(p.isVariable());
    assertTrue(t.isConstant());
    assertTrue(a.isFunctionalTerm());
    assertFalse(o.isVarTerm());
    assertFalse(p.isApplication());
    assertFalse(t.isAbstraction());
    assertFalse(a.isMetaApplication());
    assertFalse(o.isBetaRedex());
    assertTrue(p.isGround());
    assertTrue(t.isClosed());
    assertTrue(a.isTrueTerm());
    assertTrue(o.isTheoryTerm());
    assertTrue(p.isTheorySymbol());
    assertFalse(t.isValue());
    assertTrue(a.numberArguments() == 0);
    assertTrue(o.numberMetaArguments() == 0);
    assertTrue(p.queryArguments().size() == 0);
    assertTrue(t.queryHead() == t);
    assertTrue(a.queryRoot() == a);
    assertTrue(o.toValue() == null);
    assertTrue(p.toCalculationSymbol() == p);
    assertTrue(t.isFirstOrder());
    assertTrue(a.isPattern());
    assertTrue(o.isApplicative());
    assertTrue(p.queryPositions().size() == 1);
    assertTrue(t.queryPositionsForHead(t).size() == 0);
    assertTrue(a.vars().size() == 0);
    assertTrue(o.mvars().size() == 0);
    assertTrue(p.freeReplaceables().size() == 0);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testVariableRequest() {
    FunctionSymbol plus = new PlusSymbol();
    Term x = plus.queryVariable();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testAbstractionSubtermRequest() {
    FunctionSymbol times = new TimesSymbol();
    times.queryAbstractionSubterm();
  }

  @Test(expected = IndexingError.class)
  public void testArgumentPositionRequest() {
    FunctionSymbol a = new AndOrSymbol(false);
    a.querySubterm(PositionFactory.createArg(1, PositionFactory.empty));
  }

  @Test(expected = IndexingError.class)
  public void testHeadPositionRequest() {
    FunctionSymbol o = new AndOrSymbol(true);
    o.querySubterm(new HeadPosition(PositionFactory.empty, 1));
  }

  @Test(expected = IndexingError.class)
  public void testBadPositionReplacement() {
    FunctionSymbol plus = new PlusSymbol();
    plus.replaceSubterm(PositionFactory.createArg(1, PositionFactory.empty),
                        new Constant("a", baseType("a")));
  }
}
