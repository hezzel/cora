/**************************************************************************************************
 Copyright 2025--2026 Cynthia Kop

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

import java.util.Arrays;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import java.util.function.Predicate;
import charlie.types.Type;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;

/**
 * A TermPrinter specialised to printing theory terms (and: to be inherited so that theory terms
 * can be printed in different ways).
 */
public class TheoryPrinter extends TermPrinter {
  public TheoryPrinter(NameGenerator generator) {
    super(generator);
  }

  /**
   * Called by printRecursive() to print an infix symbol that is used standalone, and by the
   * default implementations of printFunctionalTerm and printApplication also for an infix symbol
   * that occurs as the root of a *partially applied* functional term [f](s1,...,sn) (with arity(f)
   * ≥ n+1).
   *
   * If the given symbol is a calculation symbol, then this deviates from the default functionality
   * by printing [calcname], where calcname is the result of the function queryCalculationName for
   * the given constant.
   */
  @Override
  protected void printSoloInfixSymbol(FunctionSymbol constant, StringBuilder builder) {
    CalculationSymbol calc = constant.toCalculationSymbol();
    if (calc == null) {
      super.printSoloInfixSymbol(constant, builder);
      return;
    }
    builder.append("[");
    builder.append(queryCalculationName(calc.queryKind(), calc.queryName(),
                                        calc.queryType()));
    builder.append("]");
  }

  /**
   * Called by printRecursive() to print a base-type term f(s), where f is a (unary) infix symbol.
   *
   * The implementation here calls either printBooleanNegation or printIntegerNegation (if s is
   * either NOT or NEGATE), or super.printPrefixTerm (otherwise).
   */
  @Override
  protected void printPrefixTerm(FunctionSymbol root, Term arg, Renaming freeNaming,
                                 MutableRenaming boundNaming, StringBuilder builder) {
    CalculationSymbol calc = root.toCalculationSymbol();
    if (calc == null || (calc.queryKind() != CalculationSymbol.Kind.NOT &&
                         calc.queryKind() != CalculationSymbol.Kind.NEGATE)) {
      super.printPrefixTerm(root, arg, freeNaming, boundNaming, builder);
      return;
    }
    String name = queryCalculationName(calc.queryKind(), calc.queryName(), calc.queryType());
    if (calc.queryKind() == CalculationSymbol.Kind.NOT) {
      printBooleanNegation(arg, freeNaming, boundNaming, builder, name);
    }
    else printIntegerNegation(arg, freeNaming, boundNaming, builder, name);
  }

  /**
   * Called by the default (TheoryPrinter) implementation of printPrefixTerm to print a term
   * NOT arg.
   * By default this will print calcname arg, or calcnamearg (without space) if calcname is a single
   * character (to support both the common uses of "not " and "!" and "¬").  Here, arg is put in
   * brackets if it is rooted by an infix symbol.
   */
  protected void printBooleanNegation(Term arg, Renaming freeNaming, MutableRenaming boundNaming,
                                      StringBuilder builder, String calcname) {
    boolean brackets = arg.isFunctionalTerm() && arg.queryRoot().isInfixSymbol();
    builder.append(calcname);
    if (calcname.length() > 1) builder.append(" ");
    if (brackets) builder.append("(");
    printRecursive(arg, freeNaming, boundNaming, builder);
    if (brackets) builder.append(")");
  }

  /**
   * Called by the default (TheoryPrinter) implementation of printPrefix to print a term
   * NEGATE arg.
   * By default this will print calcnamearg (without space in between calcname and arg),
   * where arg is put in brackets if it is either a functional term with infix root, or a negative
   * number.
   */
  protected void printIntegerNegation(Term arg, Renaming freeNaming, MutableRenaming boundNaming,
                                      StringBuilder builder, String calcname) {
    boolean brackets = arg.isFunctionalTerm() && arg.queryRoot().isInfixSymbol();
    if (!brackets && arg.isValue()) {
      Value v = arg.toValue();
      if (v.isIntegerValue() && v.getInteger().signum() < 0) brackets = true;
    }
    builder.append(calcname);
    if (brackets) builder.append("(");
    printRecursive(arg, freeNaming, boundNaming, builder);
    if (brackets) builder.append(")");
  }

  /**
   * Called by the default implementation of printInfixTerm to print the infix operator between
   * arguments s_{index-1} and s_{index}.  If the given symbol is a calculation symbol, this will
   * print " calc ", where calc is given by queryCalculationName for this symbol.
   *
   * (If the symbol is not a calculation name, super.printInfixOperator is invoked.)
   */
  @Override
  protected void printInfixOperator(FunctionSymbol f, int index, StringBuilder builder) {
    CalculationSymbol calc = f.toCalculationSymbol();
    if (calc == null) super.printInfixOperator(f, index, builder);
    else {
      builder.append(" ");
      builder.append(queryCalculationName(calc.queryKind(), calc.queryName(), calc.queryType()));
      builder.append(" ");
    }
  }

  /**
   * If the default names of the in-built calculation symbols do not suit you, then you can override
   * this to return a different name.
   */
  protected String queryCalculationName(CalculationSymbol.Kind kind, String defaultName,
                                        Type operatorType) {
    return defaultName;
  }
}

