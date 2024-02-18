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

package cora.trs;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import java.util.List;
import java.util.ArrayList;

import cora.types.Type;
import cora.types.TypeFactory;
import cora.terms.*;
import cora.reader.CoraInputReader;

public class TrsTest {
  private Type type(String txt) {
    try { return CoraInputReader.readType(txt); }
    catch (Exception e) { System.out.println(e); return null; }
  }

  private FunctionSymbol makeConstant(String name, String ty) {
    return TermFactory.createConstant(name, type(ty));
  }

  private FunctionSymbol a = makeConstant("A", "a");
  private FunctionSymbol b = makeConstant("B", "b");
  private FunctionSymbol f = makeConstant("f", "a -> b -> a");
  private FunctionSymbol g = makeConstant("g", "Int -> a");
  private FunctionSymbol h = makeConstant("h", "(a -> b) -> a -> b");
  private TRS _mstrs = null;
  private TRS _lctrs = null;
  private TRS _strs = null;
  private TRS _lcstrs = null;
  private TRS _cfs = null;
  private TRS _ams = null;
  private TRS _cora = null;

  private void setupTRSs() {
    if (_mstrs != null) return;   // we've called this before
    Alphabet alf = new Alphabet(List.of(f,g,h,a,b));
    List<Rule> empty = List.of();
    _mstrs = TrsFactory.createTrs(new Alphabet(List.of(f,g,a,b)), empty, TrsFactory.MSTRS);
    _lctrs = TrsFactory.createTrs(new Alphabet(List.of(f,g,a,b)), empty, TrsFactory.LCTRS);
    _strs = TrsFactory.createTrs(alf, empty, TrsFactory.STRS);
    _lcstrs = TrsFactory.createTrs(alf, empty, TrsFactory.LCSTRS);
    _cfs = TrsFactory.createTrs(alf, empty, TrsFactory.CFS);
    _ams = TrsFactory.createTrs(alf, empty, TrsFactory.AMS);
    _cora = TrsFactory.createTrs(alf, empty, TrsFactory.CORA);
  }

  @Test
  public void testTermsAllowedLevel() {
    setupTRSs();
    // f(a, B): a first-order term that is allowed everywhere
    Term fab = TermFactory.createApp(f, a, b);
    assertTrue(_mstrs.termAllowed(fab));
    assertTrue(_lctrs.termAllowed(fab));
    assertTrue(_strs.termAllowed(fab));
    // f(a): a higher-order term that is allowed in any of the higher-order TRSs
    Term fa = f.apply(a);
    assertFalse(_mstrs.termAllowed(fa));
    assertFalse(_lctrs.termAllowed(fa));
    assertTrue(_strs.termAllowed(fa));
    assertTrue(_lcstrs.termAllowed(fa));
    assertTrue(_cfs.termAllowed(fa));
    // h(λx.B, A): this is only allowed in those kinds where lambda is permitted
    Variable x = TermFactory.createBinder("x", type("a"));
    Term s = TermFactory.createApp(h, TermFactory.createAbstraction(x, b), a);
    assertFalse(_mstrs.termAllowed(s));
    assertFalse(_lctrs.termAllowed(s));
    assertFalse(_strs.termAllowed(s));
    assertFalse(_lcstrs.termAllowed(s));
    assertTrue(_cfs.termAllowed(s));
    assertTrue(_ams.termAllowed(s));
    assertTrue(_cora.termAllowed(s));
  }

  @Test
  public void testTermsAllowedTheories() {
    setupTRSs();
    // [+](1) and x + 3
    Term one = TheoryFactory.createValue(1);
    Term x = TermFactory.createVar("x", one.queryType());
    Term highertheory = TheoryFactory.plusSymbol.apply(one);
    Term lowertheory = TermFactory.createApp(TheoryFactory.plusSymbol, one, x);

    assertFalse(_mstrs.termAllowed(lowertheory));
    assertTrue(_lctrs.termAllowed(lowertheory));
    assertFalse(_strs.termAllowed(highertheory));
    assertFalse(_lctrs.termAllowed(highertheory));
    assertTrue(_lcstrs.termAllowed(highertheory));
    assertFalse(_cfs.termAllowed(lowertheory));
    assertFalse(_ams.termAllowed(highertheory));
    assertTrue(_cora.termAllowed(highertheory));

    // a variable of boolean type
    Term y = TheoryFactory.createVar("y", TypeFactory.boolSort);
    assertTrue(_mstrs.termAllowed(y));

    // a hidden theory symbol: (λx.a) 1
    Term abs = TermFactory.createAbstraction(TermFactory.createBinder("x", one.queryType()), a);
    Term s = abs.apply(one);
    assertFalse(_lcstrs.termAllowed(s));  // because of the lambda
    assertFalse(_cfs.termAllowed(s));     // because of the theory
    assertFalse(_ams.termAllowed(s));     // because of the theory
    assertTrue(_cora.termAllowed(s));
  }

  @Test
  public void testTermsAllowedTuples() {
    setupTRSs();
    Term x = TermFactory.createVar("x", type("a * b"));
    Term z = TermFactory.createVar("y", type("(a * b) -> c"));
    Term zx = z.apply(x);
    assertFalse(_mstrs.termAllowed(x));
    assertFalse(_lctrs.termAllowed(x));
    assertFalse(_cfs.termAllowed(zx));
    assertFalse(_lcstrs.termAllowed(z));
    assertFalse(_ams.termAllowed(zx));
    assertTrue(_cora.termAllowed(zx));
  }

  @Test
  public void testDerivedProperties() {
    Alphabet alf = new Alphabet(List.of(f, a, b));
    ArrayList<Rule> rules = new ArrayList<Rule>();
    Variable x = TermFactory.createVar("x", type("a"));
    rules.add(TrsFactory.createRule(TermFactory.createApp(f, x, b), x));
    TRS trs = TrsFactory.createTrs(alf, rules, TrsFactory.CORA);
    assertTrue(trs.theoriesIncluded());
    assertTrue(trs.tuplesIncluded());
    assertFalse(trs.isApplicative());
    // TODO: use the checkSupport function
  }
}

