/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

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

public class AriInputReaderTest {
  @Test
  public void testReadAlphabet() {
    String str =
      "(format higher-order)\n" +
      "(sort a)\n" +
      "(sort list)\n" +
      "(fun cons (-> a list list))\n" +
      "(fun map (-> list (-> a a) list))\n" +
      "(fun nil list)\n" +
      "(fun extra (-> a (-> (-> a a) a) a))\n";
    TRS trs = AriInputReader.readTrsFromString(str);
    assertTrue(trs.queryAlphabet().getSymbols().size() == 4);
    assertTrue(trs.queryAlphabet().lookup("nil").queryType().toString().equals("list"));
    assertTrue(trs.queryAlphabet().lookup("cons").queryType().toString().equals("a → list → list"));
    assertTrue(trs.queryAlphabet().lookup("map").queryType().toString().equals("list → (a → a) → list"));
    assertTrue(trs.queryAlphabet().lookup("extra").queryType().toString().equals("a → ((a → a) → a) → a"));
  }

  @Test
  public void testReadRuleWithoutMeta() {
    String str =
      "(format higher-order)\n" +
      "(sort a)\n" +
      "(sort list)\n" +
      "(fun cons (-> a list list))\n" +
      "(fun map (-> list (-> a a) list))\n" +
      "(fun nil list)\n" +
      "(fun start (-> list list))\n" +
      "(rule (map nil F) nil)\n" +
      "(rule (map (cons h t) F) (cons (F h) (map t F)))\n" +
      "(rule (start lst) (map lst (lambda ((x a)) x)))\n";
    TRS trs = AriInputReader.readTrsFromString(str);
    assertTrue(trs.queryRuleCount() == 3);
    assertTrue(trs.queryRule(0).toString().equals("map(nil, F) → nil"));
    assertTrue(trs.queryRule(1).toString().equals("map(cons(h, t), F) → cons(F(h), map(t, F))"));
    assertTrue(trs.queryRule(2).toString().equals("start(lst) → map(lst, λx.x)"));
  }

  @Test
  public void testReadRuleWithMeta() {
    String str =
      "(format higher-order)\n" +
      "(sort real)\n" +
      "(fun der (-> (-> real real) real real))\n" +
      "(fun plus (-> real real real))\n" +
      "(rule (der (lambda ((x real)) (plus (F x) (G x))))\n" +
      "      (lambda ((x real)) (plus (der (lambda ((y real)) (F y)) x)\n" +
                                     "(der (lambda ((y real)) (G y)) x))))\n";
    TRS trs = AriInputReader.readTrsFromString(str);
    assertTrue(trs.queryRuleCount() == 1);
    assertTrue(trs.queryRule(0).toString().equals(
      "der(λx.plus(F⟨x⟩, G⟨x⟩)) → λx.plus(der(λy.F⟨y⟩, x), der(λy.G⟨y⟩, x))"));
  }

  @Test
  public void testLambdaWithHigherOrderBinder() {
    String str =
      "(format higher-order)\n" +
      "(sort a)\n" +
      "(sort b)\n" +
      "(fun B b)\n" +
      "(fun f (-> (-> b (-> a b) b) a))\n" +
      "(rule (f (lambda ((y b) (x (-> a b))) (x (Z y)))) (Z B))\n";
    TRS trs = AriInputReader.readTrsFromString(str);
    assertTrue(trs.queryRuleCount() == 1);
    assertTrue(trs.queryRule(0).toString().equals("f(λy.λx.x(Z⟨y⟩)) → Z⟨B⟩"));
  }

  @Test
  public void testDuplicateBinderName() {
    String str =
      "(format higher-order)\n" +
      "(sort a)\n" +
      "(sort b)\n" +
      "(fun f (-> (-> b b) a a))\n" +
      "(fun g (-> (-> a a) a))\n" +
      "(fun A a)\n" +
      "(rule (g (lambda ((x a)) (f (lambda ((x b)) x) (Z x)))) (Z A))\n";
    TRS trs = AriInputReader.readTrsFromString(str);
    assertTrue(trs.queryRuleCount() == 1);
    assertTrue(trs.queryRule(0).toString().equals("g(λx.f(λx1.x1, Z⟨x⟩)) → Z⟨A⟩"));
  }

  @Test
  public void testBinderOverlapsMetaVariableName() {
    String str =
      "(format higher-order)\n" +
      "(sort o)\n" +
      "(fun I o)\n" +
      "(fun f (-> (-> (-> o o) o) (-> o o o) o o))\n" +
      "(rule (f (lambda ((v (-> o o))) (v I)) (lambda ((y o) (z o)) (v y z)) x) (v x I))\n";
    TRS trs = AriInputReader.readTrsFromString(str);
    assertTrue(trs.queryRuleCount() == 1);
    assertTrue(trs.queryRule(0).toString().equals("f(λv1.v1(I), λy.λz.v⟨y, z⟩, x) → v⟨x, I⟩"));
  }

  @Test
  public void testInconsistentArity() {
    String str =
      "(format higher-order)\n" +
      "(sort o)\n" +
      "(fun I o)\n" +
      "(fun f (-> (-> (-> o o) o) (-> o o o) o o))\n" +
      "(fun g (-> (-> o o) o o))\n" +
      "(rule (f (lambda ((v (-> o o))) (v I)) (lambda ((y o) (z o)) (v y z)) x) (v x))\n" +
      "(rule (g (lambda ((x o)) (Z x)) Z) I)\n";
    try { AriInputReader.readTrsFromString(str); }
    catch ( ParsingException e ) {
      assertTrue(e.getMessage().equals(
        "6:75: Meta-variable v was previously used (or declared) with arity 2, but is here " +
          "used with 1 arguments.\n" +
        "7:33: Inconsistent arity of variable Z: occurs with no arguments here, while it " +
          "previously occurred with 1.\n"));
      return;
    }
    assertTrue(false);
  }
}

