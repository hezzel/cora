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

package charlie.parser;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

import charlie.util.LookupMap;
import charlie.parser.lib.ParsingException;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.Parser.*;

public class AriParserTest {
  @Test
  public void testIncorrectFormat() {
    ErrorCollector collector = new ErrorCollector();
    try { AriParser.readProgramFromString("(format CTRS) (fun true 0)", collector); }
    catch ( ParsingException e ) {
      assertTrue(e.getMessage().equals("1:9: Format is not currently supported: CTRS\n"));
      return;
    }
    assertTrue(false);
  }

  @Test
  public void testReadDeclaredSort() {
    ParserProgram prog = AriParser.readProgramFromString(
      "(format higher-order) (sort a) (fun f a)");
    assertTrue(prog.fundecs().get("f").type().toString().equals("a"));
  }

  @Test
  public void testReadUndeclaredSort() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram prog = AriParser.readProgramFromString(
      "(format higher-order) (fun f a)", collector);
    assertTrue(prog.fundecs().get("f").type().toString().equals("a"));
    assertTrue(collector.toString().equals("1:30: Undeclared sort: a\n"));
  }

  @Test
  public void testReadArrowType() {
    ParserProgram prog = AriParser.readProgramFromString(
      "(format higher-order) (sort a) (sort b) (fun f (-> a b))");
    assertTrue(prog.fundecs().get("f").type().toString().equals("a → b"));
  }

  @Test
  public void testReadArrowTypeWithOneUndeclaredSort() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram prog = AriParser.readProgramFromString(
      "(format higher-order) (sort b) (fun f (-> b a b))", collector);
    assertTrue(prog.fundecs().get("f").type().toString().equals("b → a → b"));
    assertTrue(collector.toString().equals("1:45: Undeclared sort: a\n"));
  }

  @Test
  public void testReadArrowTypeWithProblems() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram prog = AriParser.readProgramFromString(
      "(format higher-order) (sort b) (fun f (a b)) (fun g b)", collector);
    assertTrue(prog.fundecs().get("f").type().toString().equals("a → b"));
    assertTrue(prog.fundecs().get("g").type().toString().equals("b"));
    assertTrue(collector.toString().equals(
      "1:40: Expected -> (arrow) but got IDENTIFIER (a).\n"));
  }

  @Test
  public void testReadEmptyType() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram prog = AriParser.readProgramFromString(
      "(format higher-order) (sort b) (fun f ()) (fun g b)", collector);
    assertTrue(prog.fundecs().get("f") == null);
    assertTrue(collector.toString().equals(
      "1:40: Expected -> (arrow) but got BRACKETCLOSE ()).\n"));
  }

  @Test
  public void testDoubleDeclaration() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram prog = AriParser.readProgramFromString(
      "(format higher-order)\n" +
      "(sort o)\n" +
      "(fun f (-> o o))\n" +
      "(fun f (-> o o o))", collector);
    assertTrue(collector.toString().equals(
      "4:6: Duplicate definition of function symbol f\n"));
  }

  @Test
  public void testReadCorrectHigherOrderTRS() {
    // we can parse constants nil, variables x, and identifiers with arguments
    ParserProgram program = AriParser.readProgramFromString(
      "(format higher-order)\n" +
      "(sort a)\n" +
      "(sort list)\n" +
      "(fun cons (-> a list list))\n" +
      "(fun map (-> list (-> a a) list))\n" +
      "(fun nil list)\n" +
      "(rule (map nil F) nil)\n" +
      "(rule (map (cons x l) F) (cons (F x) (map l F)))\n");
    assertTrue(program.rules().size() == 2);
    assertTrue(program.rules().get(0).toString().equals("{ [] } @(map, [nil, F]) -> nil"));
    assertTrue(program.rules().get(1).toString().equals(
      "{ [] } @(map, [@(cons, [x, l]), F]) -> @(cons, [@(F, [x]), @(map, [l, F])])"));
  }

  @Test
  public void testReadUndeclaredFunction() {
    // this is totally allowed!
    ErrorCollector collector = new ErrorCollector();
    ParserProgram program = AriParser.readProgramFromString(
      "(format higher-order)\n" +
      "(sort a)\n" +
      "(fun f (-> a a a))\n" +
      "(rule (g x x) x)\n" +
      "(rule (f x x) x)\n",
      collector
    );
    assertTrue(program.rules().size() == 2);
    assertTrue(program.rules().get(0).toString().equals("{ [] } @(g, [x, x]) -> x"));
    assertTrue(program.rules().get(1).toString().equals("{ [] } @(f, [x, x]) -> x"));
    assertTrue(collector.queryErrorCount() == 0);
  }

  @Test
  public void testLambdaTerms() {
    ParserProgram program = AriParser.readProgramFromString(
      "(format higher-order)\n" +
      "(sort a)\n" +
      "(sort b)\n" +
      "(rule (f Z) (g (lambda ((x b)) (Z x))))\n" +
      "(rule (f Z) (g (lambda ((x (-> a b)) (y a)) (Z x))))\n" +
      "(rule (app (lambda ((x a)) (Z x)) y) (Z y))\n");
    assertTrue(program.rules().size() == 3);
    assertTrue(program.rules().get(0).toString().equals(
      "{ [] } @(f, [Z]) -> @(g, [LAMBDA x::b.@(Z, [x])])"));
    assertTrue(program.rules().get(1).toString().equals(
      "{ [] } @(f, [Z]) -> @(g, [LAMBDA x::a → b.LAMBDA y::a.@(Z, [x])])"));
    assertTrue(program.rules().get(2).toString().equals(
      "{ [] } @(app, [LAMBDA x::a.@(Z, [x]), y]) -> @(Z, [y])"));
  }

  @Test
  public void testBrokenLambda() {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram program = AriParser.readProgramFromString(
      "(format higher-order)\n" +
      "(sort a)\n" +
      "(rule b (lambda () b))\n",
      collector);
    assertTrue(collector.toString().equals(
      "3:10: Lambda should have at least one variable.\n"));
  }
}

