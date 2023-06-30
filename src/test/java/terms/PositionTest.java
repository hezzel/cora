/**************************************************************************************************
 Copyright 2022, 2023 Cynthia Kop 

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

import cora.exceptions.IllegalArgumentError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.IndexingError;
import cora.types.Type;
import cora.types.TypeFactory;

public class PositionTest extends TermTestFoundation {
  @Test
  public void testEmptyPosition() {
    Position pos = new EmptyPosition();
    assertTrue(pos.toString().equals("ε"));
    assertTrue(pos.equals(new EmptyPosition()));
    assertTrue(pos.equals(new EmptyPath(TermFactory.createVar("y"))));
    assertFalse(pos.equals(new ConsPosition(1, new EmptyPosition())));
    assertTrue(pos.isEmpty());
    assertFalse(pos.isArgument());
    assertFalse(pos.isLambda());
    assertFalse(pos.isMeta());
  }

  @Test
  public void testEmptyPath() {
    Term s = TermFactory.createConstant("c", 1).apply(TermFactory.createVar("x"));
    Path p = new EmptyPath(s);
    Position pos = p;
    assertTrue(pos.toString().equals("ε"));
    assertTrue(pos.equals(new EmptyPosition()));
    assertTrue(pos.equals(new EmptyPath(TermFactory.createConstant("a", 0))));
    assertFalse(pos.equals(new ArgumentPath(s, 1, new EmptyPath(s.queryArgument(1)))));
    assertTrue(pos.isEmpty());
    assertFalse(pos.isArgument());
    assertFalse(pos.isLambda());
    assertFalse(pos.isMeta());
    assertTrue(p.queryAssociatedTerm() == s);
    assertTrue(p.queryCorrespondingSubterm() == s);
    Term t = TermFactory.createConstant("a", 0);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testNoArgumentForEmpty() {
    Position pos = new EmptyPosition();
    pos.queryArgumentPosition();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testNoMetaForEmpty() {
    Position pos = new EmptyPosition();
    pos.queryMetaPosition();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testPositionNoTail() {
    Position pos = new EmptyPosition();
    pos.queryTail();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testPathNoTail() {
    Term s = TermFactory.createConstant("c", 1).apply(TermFactory.createVar("x"));
    Path pos = new EmptyPath(s);
    pos.queryTail();
  }

  @Test
  public void testArgumentConsPosition() {
    Position pos = new ConsPosition(1, new ConsPosition(-2, new EmptyPosition()));
    assertTrue(pos.toString().equals("1.!2.ε"));
    assertTrue(pos.queryArgumentPosition() == 1);
    assertTrue(pos.queryTail().queryMetaPosition() == 2);
    assertFalse(pos.isEmpty());
    assertTrue(pos.isArgument());
    assertFalse(pos.isLambda());
    assertFalse(pos.isMeta());
    // f(g(a, b))
    Term b = TermFactory.createConstant("b", 0);
    Type triple = arrowType(TypeFactory.unitSort,
      arrowType(TypeFactory.unitSort, TypeFactory.unitSort));
    Term fgab = TermFactory.createConstant("f", 1).apply(
      TermFactory.createMeta(TermFactory.createMetaVar("g", triple, 2),
                             TermFactory.createConstant("a", 0),
                             b));
    Path path = new ArgumentPath(fgab, 1, new MetaPath(fgab.queryArgument(1), 2, new EmptyPath(b)));
    assertTrue(pos.equals(path));
  }

  @Test
  public void testArgumentPath() {
    Term b = TermFactory.createConstant("b", 0);
    Term fgab = TermFactory.createConstant("f", 1).apply(
      TermFactory.createConstant("g", 2).apply(TermFactory.createConstant("a", 0)).apply(b));
    Path path = new ArgumentPath(fgab, 1,
      new ArgumentPath(fgab.queryArgument(1), 2, new EmptyPath(b)));
    assertTrue(path.toString().equals("1.2.ε"));
    assertTrue(path.queryArgumentPosition() == 1);
    assertTrue(path.queryTail().queryArgumentPosition() == 2);
    assertFalse(path.isEmpty());
    assertTrue(path.isArgument());
    assertFalse(path.isLambda());
    assertFalse(path.isMeta());
    Position pos = new ConsPosition(1, new ConsPosition(2, new EmptyPosition()));
    assertTrue(path.equals(pos));
    assertTrue(path.queryAssociatedTerm() == fgab);
    assertTrue(path.queryCorrespondingSubterm().equals(TermFactory.createConstant("b", 0)));
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testNoMetaForArgumentPosition() {
    Position pos = new ConsPosition(2, new ConsPosition(-1, new EmptyPosition()));
    pos.queryMetaPosition();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testNoMetaForArgumentPath() {
    Term b = TermFactory.createConstant("b", 0);
    Term fgab = TermFactory.createConstant("f", 1).apply(
      TermFactory.createConstant("g", 2).apply(TermFactory.createConstant("a", 0)).apply(b));
    Path path = new ArgumentPath(fgab, 1,
      new ArgumentPath(fgab.queryArgument(1), 2, new EmptyPath(b)));
    path.queryMetaPosition();
  }

  @Test(expected = IndexingError.class)
  public void testIllegalArgumentPathCreationTooSmall() {
    Term a = TermFactory.createConstant("a", 0);
    Term fab =
      TermFactory.createConstant("f", 2).apply(a).apply(TermFactory.createConstant("b", 0));
    Path toosmall = new ArgumentPath(fab, 0, new EmptyPath(a));
  }

  @Test(expected = IndexingError.class)
  public void testIllegalArgumentPathCreationTooLarge() {
    Term b = TermFactory.createConstant("a", 0);
    Term fab =
      TermFactory.createConstant("f", 2).apply(TermFactory.createConstant("a", 0)).apply(b);
    Path toolarge = new ArgumentPath(fab, 3, new EmptyPath(b));
  }

  @Test(expected = IllegalArgumentError.class)
  public void testIllegalArgumentPathCreationBadTerms() {
    Term b = TermFactory.createConstant("a", 0);
    Term fab =
      TermFactory.createConstant("f", 2).apply(TermFactory.createConstant("a", 0)).apply(b);
    new ArgumentPath(fab, 1, new EmptyPath(b));
  }

  @Test
  public void testMetaConsPosition() {
    Position pos = new ConsPosition(-1, new ConsPosition(2, new EmptyPosition()));
    assertTrue(pos.toString().equals("!1.2.ε"));
    assertTrue(pos.queryMetaPosition() == 1);
    assertTrue(pos.queryTail().queryArgumentPosition() == 2);
    assertFalse(pos.isEmpty());
    assertFalse(pos.isArgument());
    assertFalse(pos.isLambda());
    assertTrue(pos.isMeta());
    Term b = TermFactory.createConstant("b", 0);
    MetaVariable f =
      TermFactory.createMetaVar("f", arrowType(TypeFactory.unitSort, baseType("u")), 1);
    Term fgab = TermFactory.createMeta(f,
      TermFactory.createConstant("g", 2).apply(TermFactory.createConstant("a", 0)).apply(b));
    Path path = new MetaPath(fgab, 1,
      new ArgumentPath(fgab.queryMetaArgument(1), 2, new EmptyPath(b)));
    assertTrue(pos.equals(path));
  }

  @Test
  public void testMetaPath() {
    Term b = TermFactory.createConstant("b", 0);
    MetaVariable f =
      TermFactory.createMetaVar("f", arrowType(TypeFactory.unitSort, baseType("u")), 1);
    Term fgab = TermFactory.createMeta(f,
      TermFactory.createConstant("g", 2).apply(TermFactory.createConstant("a", 0)).apply(b));
    Path path = new MetaPath(fgab, 1,
      new ArgumentPath(fgab.queryMetaArgument(1), 2, new EmptyPath(b)));
    Position pos = path;
    assertTrue(pos.toString().equals("!1.2.ε"));
    assertTrue(pos.queryMetaPosition() == 1);
    assertTrue(pos.queryTail().queryArgumentPosition() == 2);
    assertFalse(pos.isEmpty());
    assertFalse(pos.isArgument());
    assertFalse(pos.isLambda());
    assertTrue(pos.isMeta());
    Position p = new ConsPosition(-1, new ConsPosition(2, new EmptyPosition()));
    assertTrue(pos.equals(p));
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testNoArgumentForMetaPosition() {
    Position pos = new ConsPosition(-1, new ConsPosition(2, new EmptyPosition()));
    pos.queryArgumentPosition();
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testNoArgumentForMetaPath() {
    Term b = TermFactory.createConstant("b", 0);
    MetaVariable f =
      TermFactory.createMetaVar("f", arrowType(TypeFactory.unitSort, arrowType("u", "u")), 1);
    Term fgabc = TermFactory.createMeta(f,    // f⟨g(a),b⟩(c)
      TermFactory.createConstant("g", 2).apply(TermFactory.createConstant("a", 0)).apply(b))
        .apply(constantTerm("c", baseType("u")));
    Path path = new MetaPath(fgabc, 1,
      new ArgumentPath(fgabc.queryMetaArgument(1), 2, new EmptyPath(b)));
    path.queryArgumentPosition();
  }

  @Test(expected = IndexingError.class)
  public void testIllegalMetaPathCreationNoMeta() {
    // f(g(a, b))
    Term b = TermFactory.createConstant("b", 0);
    Type triple = arrowType(TypeFactory.unitSort,
      arrowType(TypeFactory.unitSort, TypeFactory.unitSort));
    Term fgab = TermFactory.createConstant("f", 1).apply(
      TermFactory.createMeta(TermFactory.createMetaVar("g", triple, 2),
                             TermFactory.createConstant("a", 0),
                             b));
    Path path = new MetaPath(fgab, 1, new MetaPath(fgab.queryArgument(1), 2, new EmptyPath(b)));
  }

  @Test(expected = IndexingError.class)
  public void testIllegalMetaPathCreationTooSmall() {
    Term a = TermFactory.createConstant("a", baseType("A"));
    Term b = TermFactory.createConstant("b", baseType("B"));
    MetaVariable z =
      TermFactory.createMetaVar("z", arrowType(baseType("A"), arrowType("B", "C")), 2);
    Term zab = TermFactory.createMeta(z, a, b);
    Path toosmall = new MetaPath(zab, 0, new EmptyPath(a));
  }

  @Test(expected = IndexingError.class)
  public void testIllegalMetaPathCreationTooLarge() {
    Term a = TermFactory.createConstant("a", baseType("A"));
    Term b = TermFactory.createConstant("b", baseType("B"));
    MetaVariable z =
      TermFactory.createMetaVar("z", arrowType(baseType("A"), arrowType("B", "C")), 2);
    Term zab = TermFactory.createMeta(z, a, b);
    Path toosmall = new MetaPath(zab, 3, new EmptyPath(b));
  }

  @Test(expected = IllegalArgumentError.class)
  public void testIllegalMetaPathCreationBadTerms() {
    Term a = TermFactory.createConstant("a", baseType("A"));
    Term b = TermFactory.createConstant("b", baseType("B"));
    MetaVariable z =
      TermFactory.createMetaVar("z", arrowType(baseType("A"), arrowType("B", "C")), 2);
    Term zab = TermFactory.createMeta(z, a, b);
    Path toosmall = new MetaPath(zab, 2, new EmptyPath(a));
  }

  @Test
  public void testLambdaConsPosition() {
    Position empty = new EmptyPosition();
    Position pos = new ConsPosition(0, new ConsPosition(1, new ConsPosition(0, empty)));
    assertTrue(pos.toString().equals("0.1.0.ε"));
    assertFalse(pos.isArgument());
    assertTrue(pos.isLambda());
    assertFalse(pos.isEmpty());
    assertTrue(pos.queryTail().queryArgumentPosition() == 1);
    
    Type o = TypeFactory.unitSort;
    Variable x = new Binder("x", o);
    Variable y = new Binder("y", o);
    Term g = new Constant("g", arrowType(arrowType(o, o), o));
    Term f = new Constant("f", arrowType(o, o));
    Term fx = f.apply(x);
    Term xfx = new Abstraction(x, fx);
    Term gxfx = g.apply(xfx);
    Term term = new Abstraction(y, gxfx);
    Path path = new LambdaPath(term, new ArgumentPath(gxfx, 1, new LambdaPath(xfx,
      new EmptyPath(fx))));
    assertTrue(pos.equals(path));
    assertTrue(path.equals(pos));
  }

  @Test
  public void testLambdaPath() {
    Type o = TypeFactory.unitSort;
    Variable x = new Binder("x", o);
    Variable y = new Binder("y", o);
    Term g = new Constant("g", arrowType(arrowType(o, o), o));
    Term f = new Constant("f", arrowType(o, o));
    Term fx = f.apply(x);
    Term xfx = new Abstraction(x, fx);
    Term gxfx = g.apply(xfx);
    Term term = new Abstraction(y, gxfx); // λy.g(λx.f(x))
    Path path = new LambdaPath(term, new ArgumentPath(gxfx, 1, new LambdaPath(xfx,
      new EmptyPath(fx))));

    assertTrue(path.toString().equals("0.1.0.ε"));
    assertFalse(path.isArgument());
    assertTrue(path.isLambda());
    assertFalse(path.isEmpty());
    assertTrue(path.queryTail().queryArgumentPosition() == 1);
    assertTrue(path.queryAssociatedTerm() == term);
    assertTrue(path.queryCorrespondingSubterm() == fx);
  }

  @Test
  public void testLambdaPathInApplication() {
    Type o = TypeFactory.unitSort;
    Variable x = new Binder("x", o);
    Variable y = new Binder("y", o);
    Term g = new Constant("g", arrowType(arrowType(o, o), o));
    Term f = new Constant("f", arrowType(o, o));
    Term fx = f.apply(x);
    Term xfx = new Abstraction(x, fx);
    Term gxfx = g.apply(xfx);
    Term abs = new Abstraction(y, gxfx); // λy.g(λx.f(x))
    Term term = new Application(abs, new Constant("a", TypeFactory.createSort("o")));
    Path path = new LambdaPath(term, new ArgumentPath(gxfx, 1, new LambdaPath(xfx,
      new EmptyPath(fx))));

    assertTrue(path.toString().equals("0.1.0.ε"));
    assertFalse(path.isArgument());
    assertTrue(path.isLambda());
    assertFalse(path.isEmpty());
    assertTrue(path.queryTail().queryArgumentPosition() == 1);
    assertTrue(path.queryAssociatedTerm() == term);
    assertTrue(path.queryCorrespondingSubterm() == fx);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testNoArgumentForLambda() {
    Position empty = new EmptyPosition();
    Position pos = new ConsPosition(0, new ConsPosition(1, new ConsPosition(0, empty)));
    pos.queryArgumentPosition();
  }

  @Test(expected = IllegalArgumentError.class)
  public void testIllegalLambdaPathCreationDifferentTerms() {
    Variable x = new Binder("x", TypeFactory.unitSort);
    Term term = new Abstraction(x, x);
    new LambdaPath(term, new EmptyPath(term));
  }

  @Test
  public void testCorrectParsing() {
    Position pos = PositionFactory.parsePos("5.6.7");
    assertTrue(pos.toString().equals("5.6.7.ε"));
    pos = PositionFactory.parsePos("19.!12.ε");
    assertTrue(pos.toString().equals("19.!12.ε"));
    pos = PositionFactory.parsePos("!2.1.");
    assertTrue(pos.toString().equals("!2.1.ε"));
    pos = PositionFactory.parsePos("0.19.12.ε");
    assertTrue(pos.toString().equals("0.19.12.ε"));
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithAsciiStar() {
    PositionFactory.parsePos("1.254.*3.☆15");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithUniStar() {
    PositionFactory.parsePos(("3.111.☆2"));
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithEmptyIndex() {
    PositionFactory.parsePos("1..254");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithEmptyIndexAtTheEnd() {
    PositionFactory.parsePos("1.254.3..");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithNegativeIndex() {
    PositionFactory.parsePos("19.-1.12.ε");
  }

  @Test(expected = cora.exceptions.ParserError.class)
  public void testParseWithIllegalCharacter() {
    PositionFactory.parsePos("5.1@.3");
  }
}

