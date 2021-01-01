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
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;

/**
 * This class tests whether the substitute function is correctly implemented in all kinds of terms.
 */
public class TermSubstitutionTest extends TermTestInherit {
  @Test
  public void testSubstituteSimpleLinearTerm() {
    Variable x = freeVariable("x", arrowType("o", "o"));   // x : o -> o
    Variable y = binderVariable("y", new ArrowType(baseType("o"), arrowType("o", "o")));
                                                           // y : o -> o -> o
    Variable z = binderVariable("z", baseType("o"));       // z : o
    Term a = constantTerm("a", baseType("o"));             // a : o
    // term := f(x, y(a, z))
    Term term = binaryTerm("f", arrowType("σ", "τ"), x, new VarTerm(y, a, z));
    // substitute only x and z
    Substitution subst = new Subst();
    subst.extend(x, unaryTerm("g", arrowType("o", "o"), a));
                                                           // [x := g(a)]
    subst.extend(z, binaryTerm("g", baseType("o"), a, a)); // [z := g(a,a)]
    // f(x, y(a,z)) [x := g(a), z := g(a,a)] should be f(g(a), y(a, g(a, a)))
    Term result = term.substitute(subst);
    assertTrue(result.toString().equals("f(g(a), y(a, g(a, a)))"));
  }

  @Test
  public void testSubstituteSimpleNonLinearTerm() {
    Variable x = freeVariable("x", arrowType("o", "o"));   // x : o -> o
    Variable y = binderVariable("y", new ArrowType(arrowType("o", "o"), arrowType("o", "o")));
                                                           // y : (o -> o) -> o -> o
    Variable z = binderVariable("z", baseType("o"));       // z : o
    // term := f(x, y(x, z))
    Term term = binaryTerm("f", baseType("output"), x, new VarTerm(y, x, z));
    // substitute [x:=λu.g(a,u), z:=b]
    Term a = constantTerm("a", baseType("o"));
    Term b = constantTerm("b", baseType("o"));
    Variable u = binderVariable("u", baseType("o"));
    Term gau = binaryTerm("g", baseType("o"), a, u);
    Term abs = new Abstraction(u, gau);
    Substitution subst = new Subst();
    subst.extend(x, abs);
    subst.extend(z, b);
    // f(x, y(x, z)) [x:=λu.g(a,u), z:=b] should be f(λu.g(a, u), y(λu.g(a, u), b))
    Term result = term.substitute(subst);
    Term expected = binaryTerm("f", baseType("output"), abs, new VarTerm(y, abs, b));
    assertTrue(result.equals(expected));
  }

  @Test
  public void testSubstituteBelowAbstraction() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = freeVariable("y", arrowType("o", "o"));
    Variable z = binderVariable("z", baseType("o"));
    // term := f(λx.g(x, f(y, z)))
    Term fyz = binaryTerm("f", baseType("o"), y, z);
    Term gxfyz = binaryTerm("g", baseType("o"), x, fyz);
    Term term = unaryTerm("f", arrowType("o", "o"), new Abstraction(x, gxfyz));
    // [y := λz.z, z := a]
    Substitution subst = new Subst();
    Term abs = new Abstraction(z, z);
    Term a = constantTerm("a", baseType("o"));
    subst.extend(y, abs);
    subst.extend(z, a);
    // f(λx.g(x, f(y, z)() [y := λz.z, z := a] = f(λx.g(x, f(λz.z, a)))]
    Term result = term.substitute(subst);
    Term expected = unaryTerm("f", arrowType("o", "o"), new Abstraction(x,
      binaryTerm("g", baseType("o"), x, binaryTerm("f", baseType("o"), abs, a))));
    assertTrue(result.equals(expected));
  }

  @Test
  public void testSubstituteBelowAbstractionReuseAbstractionVariable() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = freeVariable("y", arrowType("o", "o"));
    Variable z = binderVariable("z", baseType("o"));
    // term := f(λx.g(x, f(y, z)))
    Term fyz = binaryTerm("f", baseType("o"), y, z);
    Term gxfyz = binaryTerm("g", baseType("o"), x, fyz);
    Term term = unaryTerm("f", arrowType("o", "o"), new Abstraction(x, gxfyz));
    // [y := λx.x, z := a]
    Substitution subst = new Subst();
    Term a = constantTerm("a", baseType("o"));
    subst.extend(y, new Abstraction(x,x));
    subst.extend(z, a);
    // f(λx.g(x, f(y, z)() [y := λx.x, z := a] = f(λx.g(x, f(λz.z, a)))]
    Term result = term.substitute(subst);
    Term expected = unaryTerm("f", arrowType("o", "o"), new Abstraction(x,
      binaryTerm("g", baseType("o"), x, binaryTerm("f", baseType("o"),
      new Abstraction(z, z), a))));
    assertTrue(result.equals(expected));
  }

  @Test
  public void testSubstituteToBoundVariable() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = freeVariable("y", arrowType("o", "o"));
    Variable z = binderVariable("z", baseType("o"));
    // term := f(λx.g(x, f(y, z)))
    Term fyz = binaryTerm("f", baseType("o"), y, z);
    Term gxfyz = binaryTerm("g", baseType("o"), x, fyz);
    Term term = unaryTerm("f", arrowType("o", "o"), new Abstraction(x, gxfyz));
    // [y:=h, z:=x]
    Substitution subst = new Subst();
    Term h = constantTerm("h", arrowType("o", "o"));
    subst.extend(y, h);
    subst.extend(z, x);
    // f(λx.g(x, f(y, z))) [y:=h, z:=x] = f(λu.g(u, f(h, x))) = f(λz.g(z, f(h,x)))
    Term result = term.substitute(subst);
    Term expected = unaryTerm("f", arrowType("o", "o"), new Abstraction(z,
      binaryTerm("g", baseType("o"), z, binaryTerm("f", baseType("o"), h, x))));
    assertTrue(result.equals(expected));
  }

  @Test
  public void testAttemptToSubstituteBoundVariable() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = freeVariable("y", arrowType("o", "o"));
    Variable z = binderVariable("z", baseType("o"));
    // term := f(λx.g(x, f(y, z)))
    Term fyz = binaryTerm("f", baseType("o"), y, z);
    Term gxfyz = binaryTerm("g", baseType("o"), x, fyz);
    Term term = unaryTerm("f", arrowType("o", "o"), new Abstraction(x, gxfyz));
    // [x:=a, y:=h, z:=b]
    Substitution subst = new Subst();
    Term a = constantTerm("a", baseType("o"));
    Term b = constantTerm("b", baseType("o"));
    Term h = constantTerm("h", arrowType("o", "o"));
    subst.extend(x, a);
    subst.extend(y, h);
    subst.extend(z, b);
    // f(λx.g(x, f(y, z))) [x:=a, y:=h, z:=b] = f(λx.g(x, f(h, b)))
    Term result = term.substitute(subst);
    Term expected = unaryTerm("f", arrowType("o", "o"), new Abstraction(x,
      binaryTerm("g", baseType("o"), x,  binaryTerm("f", baseType("o"), h, b))));
    assertTrue(result.equals(expected));
  }

  @Test
  public void testSubstituteVartermWithNonAbstraction() {
    Variable x = binderVariable("x", baseType("o"));
    Variable y = freeVariable("y", new ArrowType(baseType("o"), arrowType("bb", "cc")));
    Variable z = freeVariable("z", baseType("bb"));
    Variable u = binderVariable("u", new ArrowType(arrowType("o","o"), baseType("bb")));
    Variable v = freeVariable("v", arrowType("o", "o"));
    // term = f(x, y(a, z), u(v)) : o
    Term a = constantTerm("a", baseType("o"));
    Term term = binaryTerm("f", arrowType("bb", "o"), x, new VarTerm(y, a, z)).apply(
      new VarTerm(u, v));
    // subst = [x := g(a), y := h(b), z := p(z,z), u := u'(z,v), v:= g]
    Substitution subst = new Subst();
    Term b = constantTerm("b", baseType("aa"));
    subst.extend(x, unaryTerm("g", baseType("o"), a));
    subst.extend(y, unaryTerm("h", y.queryType(), b));
    subst.extend(z, binaryTerm("p", baseType("bb"), z, z));
    Variable newu = freeVariable("u", new ArrowType(baseType("bb"), new ArrowType(v.queryType(),
      u.queryType())));
    subst.extend(u, new VarTerm(newu, z, v));
    subst.extend(v, constantTerm("g", arrowType("o", "o")));
    // term subst = f(g(a), h(b, a, p(z, z)), u(z, v, g))
    Term result = term.substitute(subst);
    assertTrue(result.toString().equals("f(g(a), h(b, a, p(z, z)), u(z, v, g))"));
  }

  @Test
  public void testSubstituteVartermWithAbstraction() {
    Variable x = binderVariable("x", new ArrowType(arrowType("o","o"), baseType("o")));
    Variable y = freeVariable("y", new ArrowType(baseType("o"), arrowType("o", "o")));
    Variable z = freeVariable("z", baseType("o"));
    Variable v = freeVariable("v", arrowType("o", "o"));
    // term = f(y(a, z), x(v))
    Term a = constantTerm("a", baseType("o"));
    Term term = binaryTerm("f", baseType("o"), new VarTerm(y, a, z), new VarTerm(x, v));
    // subst = [x := λu:o→o.u(a), y := λv:o,w:o.g(w,v), z := g(a,b), v := h]
    Term b = constantTerm("b", baseType("o"));
    Term h = constantTerm("h", arrowType("o", "o"));
    Variable u = binderVariable("u", arrowType("o", "o"));
    Variable vv = binderVariable("v", baseType("o"));
    Variable w = binderVariable("w", baseType("o"));
    Substitution subst = new Subst();
    subst.extend(x, new Abstraction(u, new VarTerm(u, a)));
    subst.extend(y, new Abstraction(vv, new Abstraction(w, binaryTerm("g", baseType("o"), w, vv))));
    subst.extend(z, binaryTerm("g", baseType("o"), a, b));
    subst.extend(v, h);
    // term subst = f(g(g(a, b), a), h(a))
    Term result = term.substitute(subst);
    assertTrue(result.toString().equals("f(g(g(a, b), a), h(a))"));
  }

  @Test
  public void testSubstituteCausingRepeatedBeta() {
    Variable x = binderVariable("x", new ArrowType(arrowType("o","o"), baseType("o")));
    Variable z = freeVariable("z", new ArrowType(baseType("o"), arrowType("o", "o")));
    Variable y = freeVariable("y", new ArrowType(baseType("o"), new ArrowType(z.queryType(),
      baseType("o"))));
    Variable v = freeVariable("v", arrowType("o", "o"));
    // term = f(y(a, z), x(v))
    Term a = constantTerm("a", baseType("o"));
    Term term = binaryTerm("f", baseType("o"), new VarTerm(y, a, z), new VarTerm(x, v));
    // subst = [x := λF.F(F(a)), y := λu:o.λG:o→o→o.G(b,u), z := λi:o.λj:o.i, v := λu:o.g(u,u)]
    Substitution subst = new Subst();
    Term b = constantTerm("b", baseType("o"));
    Variable u = binderVariable("u", baseType("o"));
    Variable i = binderVariable("i", baseType("o"));
    Variable f = binderVariable("F", arrowType("o", "o"));
    Variable g = binderVariable("G", new ArrowType(baseType("o"), arrowType("o", "o")));
    subst.extend(x, new Abstraction(f, new VarTerm(f, new VarTerm(f, a))));
    subst.extend(y, new Abstraction(u, new Abstraction(g, new VarTerm(g, b, u))));
    subst.extend(z, new Abstraction(i, new Abstraction(u, i)));
    subst.extend(v, new Abstraction(u, binaryTerm("g", baseType("o"), u, u)));
    // term subst = f( (λu.λG.G(b,u)) * [a, (λi.λj.i)] , (λF.F(F(a))) * [λu.g(u,u)]
    //            = f( (λG.G(b,a)) * [λi.λj.i] , (λF.F(F(a))) * [λu.g(u,u)]
    //            = f( (λi.λj.i) * [b, a] , (λF.F(F(a))) * [λu.g(u,u)]
    //            = f( b , (λF.F(F(a))) * [λu.g(u,u)]
    //            = f( b , (λu.g(u,u)) * [(λu.g(u,u)) * [a]] )
    //            = f( b , (λu.g(u,u)) * [g(a,a)] )
    //            = f( b , g( g(a,a), g(a,a) ) )
    Term result = term.substitute(subst);
    assertTrue(result.toString().equals("f(b, g(g(a, a), g(a, a)))"));
  }
}

