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

package cora.termination.transformation;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.ArrayList;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import charlie.terms.*;
import charlie.trs.*;
import charlie.reader.CoraInputReader;
import cora.io.*;
import cora.termination.transformation.HelperFunctionTransformer.Candidate;

public class HelperFunctionTransformerTest {
  private TRS makeTrs(String txt) {
    return CoraInputReader.readTrsFromString(txt, TrsFactory.LCSTRS);
  }

  @Test
  public void testRuleArity() {
    TRS trs = makeTrs(
      "f :: Int -> Int -> Int\n" +
      "g :: Int -> (Int -> Int) -> Int\n" +
      "h :: (Int -> Int) -> Int\n" +
      "i :: Int -> Int\n" +
      "j :: Int -> Int -> Int\n" +
      "const :: Int -> Int -> Int\n" +
      "f(x,y) -> x f(0) -> const(0)\n" +
      "g(x) -> h g(0,i) -> 1\n" +
      "h(F) -> F(0)\n" +
      "j(x,y) -> 0\n" +
      "const(x,y) -> y\n");
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    assertTrue(transformer.queryRuleArity(trs.lookupSymbol("f")) == 1);
    assertTrue(transformer.queryRuleArity(trs.lookupSymbol("g")) == 1);
    assertTrue(transformer.queryRuleArity(trs.lookupSymbol("h")) == 1);
    assertTrue(transformer.queryRuleArity(trs.lookupSymbol("j")) == 2);
    assertTrue(transformer.queryRuleArity(trs.lookupSymbol("i")) == null);
  }

  @Test
  public void testReplacementCandidates() {
    TRS trs = makeTrs(
      "O :: Nat\n" +
      "s :: Nat -> Nat\n" +
      "add :: Nat -> Nat -> Nat\n" +
      "id :: Nat -> Nat\n" +
      "f :: Nat -> Nat -> Nat\n" +
      "g :: (Nat -> Nat) -> Nat\n" +
      "h :: (Nat -> Nat) -> (Nat -> Nat) -> (Nat -> Nat -> Nat) -> (Nat -> Nat) -> " +
           "(Nat -> Nat) -> Nat\n" +
      "q :: Nat -> Nat -> Nat\n" +
      "add(x, s(y)) -> id(add(s(x), y))\n" +
      "id(x) -> id(id(x))\n" +
      "f(x,y) -> g(f(x))\n" +
      "g(id) -> O\n" +
      "q(x,y) -> g(q(x))\n" +
      "q(O) -> s\n" +
      "add(s(x), y) -> h(add(x), add(s(x)), add, add(y), f(s(x)))\n"
    );
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    ArrayList<HelperFunctionTransformer.Candidate> cands = transformer.getReplacementCandidates();
    assertTrue(cands.get(0).below().equals(trs.lookupSymbol("g")));
    assertTrue(cands.get(0).argument() == 1);
    assertTrue(cands.get(0).main().equals(trs.lookupSymbol("f")));
    assertTrue(cands.get(0).numArgs() == 1);
    assertTrue(cands.get(1).below().equals(trs.lookupSymbol("h")));
    assertTrue(cands.get(1).argument() == 2);
    assertTrue(cands.get(1).main().equals(trs.lookupSymbol("add")));
    assertTrue(cands.get(1).numArgs() == 1);
    assertTrue(cands.get(2).below().equals(trs.lookupSymbol("h")));
    assertTrue(cands.get(2).argument() == 3);
    assertTrue(cands.get(2).main().equals(trs.lookupSymbol("add")));
    assertTrue(cands.get(2).numArgs() == 0);
    // (q,1,g,1) is NOT a candidate, since q has rule arity 1
  }

  /* in case we only want private functions to be changeable under some settings
  @Test
  public void testUnsuitablePrivate() {
    TRS trs = makeTrs(
      "private f :: (Int -> Int) -> Int\n" +
      "public  g :: (Int -> Int) -> Int -> Int\n" +
      "public  h :: Int -> Int\n" +
      "public  i :: (Int -> Int) -> Int\n" +
      "private j :: (Int -> Int) -> Int\n" +
      "public  a :: Int -> Int\n" +
      "f(X) -> 0\n" +
      "g(X, 0) -> 0\n" +
      "h(i(X)) -> 0\n" +
      "h(j(X)) -> 0\n" +
      "g(X, 1) -> 0\n"
    );
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    FunctionSymbol h = trs.lookupSymbol("h");
    FunctionSymbol i = trs.lookupSymbol("i");
    FunctionSymbol j = trs.lookupSymbol("j");
    FunctionSymbol a = trs.lookupSymbol("a");
    assertTrue(transformer.checkCandidateSuitability(new Candidate(f, 1, a, 0)));
    assertFalse(transformer.checkCandidateSuitability(new Candidate(g, 1, a, 0)));
    assertFalse(transformer.checkCandidateSuitability(new Candidate(i, 1, a, 0)));
    assertTrue(transformer.checkCandidateSuitability(new Candidate(j, 1, a, 0)));
  }
  */

  @Test
  public void testUnsuitability() {
    TRS trs = makeTrs(
      "f :: Int -> (Int -> Int) -> Int\n" +
      "g :: (Int -> Int) -> Int -> Int\n" +
      "h :: (Int -> Int) -> Int\n" +
      "a :: Int -> Int\n" +
      "b :: Int -> Int\n" +
      "f(0) -> f(1)\n" +
      "g(X, 0) -> g(X, 1)\n" +
      "g(a, 0) -> g(a, 1)\n" +
      "{X :: Int -> Int -> Int} h(X(0)) -> 0\n"
    );
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    FunctionSymbol f = trs.lookupSymbol("f");
    FunctionSymbol g = trs.lookupSymbol("g");
    FunctionSymbol h = trs.lookupSymbol("h");
    FunctionSymbol a = trs.lookupSymbol("a");
    FunctionSymbol b = trs.lookupSymbol("b");
    assertFalse(transformer.checkCandidateSuitability(new Candidate(f, 2, a, 0)));
    assertFalse(transformer.checkCandidateSuitability(new Candidate(g, 1, a, 0)));
    assertTrue(transformer.checkCandidateSuitability(new Candidate(g, 1, b, 0)));
  }

  private FunctionSymbol makeConstant(String name, String type, TreeSet<FunctionSymbol> addto) {
    FunctionSymbol ret = TermFactory.createConstant(name, CoraInputReader.readType(type));
    addto.add(ret);
    return ret;
  }

  @Test
  public void testCreateCopies() {
    TreeSet<FunctionSymbol> symbols = new TreeSet<FunctionSymbol>();
    FunctionSymbol f = makeConstant("f", "o -> (o -> o) -> o", symbols);
    FunctionSymbol g = makeConstant("g", "o -> o -> o", symbols);
    FunctionSymbol gprime = makeConstant("g'", "w -> w", symbols);
    FunctionSymbol h = makeConstant("h", "(w -> w) -> (o -> o) -> o -> o", symbols);
    FunctionSymbol a = makeConstant("a", "w -> w -> o -> o", symbols);
    ArrayList<Candidate> candidates = new ArrayList<Candidate>();
    candidates.add(new Candidate(f, 2, g, 1));
    candidates.add(new Candidate(h, 2, g, 1));
    candidates.add(new Candidate(h, 1, gprime, 0));
    candidates.add(new Candidate(f, 2, a, 2));
    // (f,2,g,1) (h,2,g,1), (h,1,g',0) (f,2,a,2)

    TRS trs = TrsFactory.createTrs(new Alphabet(symbols), new ArrayList<Rule>(), TrsFactory.LCSTRS);
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    TreeMap<FunctionSymbol,FunctionSymbol> replacements = transformer.createCopies(candidates);
    assertTrue(replacements.size() == 3);
    assertTrue(replacements.get(f) == null);
    assertTrue(replacements.get(g).queryName().equals("g'0"));
    assertTrue(replacements.get(g).queryType().equals(g.queryType()));
    assertTrue(replacements.get(gprime).queryName().equals("g''"));
    assertTrue(replacements.get(gprime).queryType().equals(gprime.queryType()));
    assertTrue(replacements.get(a).queryName().equals("a'"));
    assertTrue(replacements.get(a).queryType().equals(a.queryType()));
  }

  @Test
  public void testRenaming() {
    TRS trs = makeTrs(
      "f :: (o -> o) -> o\n" +
      "g :: o -> o -> o\n" +
      "a :: o\n" +
      "g(x,y) -> f(g(x))\n"
    );
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    ArrayList<HelperFunctionTransformer.Candidate> cands = transformer.getReplacementCandidates();
    TreeMap<FunctionSymbol,FunctionSymbol> replacements = transformer.createCopies(cands);
    Term term = CoraInputReader.readTerm("g(f(g(f(g(a)))))", trs);
    term = transformer.renameSymbolsInsideCandidates(term, cands, replacements);
    assertTrue(term.toString().equals("g(f(g'(f(g'(a)))))"));
  }

  @Test
  public void testApplyAllUpdates() {
    TRS trs = makeTrs(
      "f :: Int -> Bool -> Int -> A\n" +
      "g :: (Int -> Int -> A) -> (Int -> A) -> (Int -> Int -> A) -> B\n" +
      "h :: Int -> Int -> A\n" +
      "a :: B -> A\n" +
      "b :: A -> (Int -> A) -> A\n" +
      "a(g(X, Y, Z)) -> b(Y(0), Z(1))\n"
    );

    ArrayList<Candidate> cands = new ArrayList<Candidate>();
    cands.add(new Candidate(trs.lookupSymbol("g"), 1, trs.lookupSymbol("h"), 0));
    cands.add(new Candidate(trs.lookupSymbol("g"), 3, trs.lookupSymbol("h"), 0));
    cands.add(new Candidate(trs.lookupSymbol("g"), 2, trs.lookupSymbol("h"), 1));
    cands.add(new Candidate(trs.lookupSymbol("g"), 2, trs.lookupSymbol("f"), 2));
    
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    TreeMap<FunctionSymbol,FunctionSymbol> renamings = transformer.createCopies(cands);
    // but now we use those substitutions to get updates
    ArrayList<Rule> rules = transformer.getInstantiatedCopies(trs.queryRule(0), cands, renamings);
    assertTrue(rules.size() == 6);
    // substitution: []
    assertTrue(rules.get(0).toString().equals("a(g(X, Y, Z)) → b(Y(0), Z(1))"));
    // substitution: [Z:=h]
    assertTrue(rules.get(1).toString().equals("a(g(X, Y, h')) → b(Y(0), h(1))"));
    // substitution: [Y:=h(x1)]
    assertTrue(rules.get(2).toString().equals("a(g(X, h'(arg.3.1), Z)) → b(h(arg.3.1, 0), Z(1))"));
    // substitution: [Y:=h(x1), Z:=h]
    assertTrue(rules.get(3).toString().equals("a(g(X, h'(arg.3.1), h')) → b(h(arg.3.1, 0), h(1))"));
    // substitution: [Y:=f(x1,x2)]
    assertTrue(rules.get(4).toString().equals(
      "a(g(X, f'(arg.4.1, arg.4.2), Z)) → b(f(arg.4.1, arg.4.2, 0), Z(1))"));
    // substitution: [Y:=f(x1,x2), Z:=h]
    assertTrue(rules.get(5).toString().equals(
      "a(g(X, f'(arg.4.1, arg.4.2), h')) → b(f(arg.4.1, arg.4.2, 0), h(1))"));
  }

  @Test
  public void testNotApplicable() {
    TRS trs = makeTrs(
      "a :: o\n" +
      "b :: o\n" +
      "f :: o -> o -> o\n" +
      "g :: (o -> o) -> o\n" +
      "h :: o -> o -> Bool\n" +
      "f(x, a) -> g(f(x))\n" +
      "g(Z) -> Z(b)\n" +
      "h(x,x) -> true\n"
    );
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    HelperFunctionTransformer.TransformerProofObject tpo = transformer.transform();
    assertTrue(tpo.queryAnswer() == ProofObject.Answer.NO);
    OutputModule module = OutputModule.createPlainModule(trs);
    tpo.justify(module);
    assertTrue(module.toString().equals("The TRS does not satisfy the conditions to " +
      "apply the helper function transformation.\n\n"));
  }

  @Test
  public void testNoCandidates() {
    TRS trs = makeTrs(
      "a :: o\n" +
      "b :: o\n" +
      "f :: o -> o -> o\n" +
      "g :: (o -> o) -> o\n" +
      "h :: o -> o -> o\n" +
      "f(x, a) -> g(h(x))\n" +
      "h(x, y) -> y\n" +
      "g(Z) -> Z(b)\n"
    );
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    HelperFunctionTransformer.TransformerProofObject tpo = transformer.transform();
    assertTrue(tpo.queryAnswer() == ProofObject.Answer.MAYBE);
    OutputModule module = OutputModule.createPlainModule(trs);
    tpo.justify(module);
    assertTrue(module.toString().equals("The helper function transformation was not applied: " +
      "I could not find any candidate positions to replace.\n\n"));
  }

  @Test
  public void testTransformSuccess() {
    TRS trs = makeTrs(
      "a :: o\n" +
      "b :: o\n" +
      "f :: o -> o -> o\n" +
      "g :: (o -> o) -> o\n" +
      "f(x, a) -> g(f(x))\n" +
      "g(Z) -> Z(b)\n"
    );
    HelperFunctionTransformer transformer = new HelperFunctionTransformer(trs);
    HelperFunctionTransformer.TransformerProofObject tpo = transformer.transform();
    assertTrue(tpo.queryAnswer() == ProofObject.Answer.YES);
    assertTrue(tpo.queryResultingTRS().toString().equals(
      "Σ = {\n" +
      "  a :: o\n" +
      "  b :: o\n" +
      "  f :: o → o → o\n" +
      "  f' :: o → o → o  (private)\n" +
      "  g :: (o → o) → o\n" +
      "} ∪ Σ_{theory}\n" +
      "R = {\n" +
      "  f(x, a) → g(f'(x))\n" +
      "  g(Z) → Z(b)\n" +
      "  g(f'(arg.1.1)) → f(arg.1.1, b)\n" +
      "}\n" +
      "We also include the following rule schemes: Calc\n"));
    OutputModule module = OutputModule.createPlainModule(trs);
    tpo.justify(module);
    assertTrue(module.toString().equals(
      "We observe that the TRS can be modified, without affecting termination, in the following way:"
      + "\n\n" +
      "  We replace all occurrences of g(f(y{1})) by g(f'(y{1})).\n\n" +
      "This yields a(n) LCSTRS with only rule scheme Calc:\n\n" +
      "  Signature: a  :: o\n" +
      "             b  :: o\n" +
      "             f  :: o -> o -> o\n" +
      "             f' :: o -> o -> o   (private)\n" +
      "             g  :: (o -> o) -> o\n\n" +
      "  Rules: f(x, a) -> g(f'(x))\n" +
      "         g(Z) -> Z(b)\n" +
      "         g(f'(arg.1.1)) -> f(arg.1.1, b)\n\n"));
  }
}

