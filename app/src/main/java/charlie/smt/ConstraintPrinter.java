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

package charlie.smt;

import charlie.util.Pair;

/**
 * ConstraintPrinters are used in the overall output process of the tool.  This class provides a
 * default implementation, but is meant to be inherited.  You can for instance instantiate the
 * ConstraintPrinter to use unicode symbols, ascii-art, html, print smt-lib style or whatever is
 * needed.
 */
public class ConstraintPrinter {
  /** The printer used to print expressions below a Comparison */
  protected IExpPrinter _expPrinter;
  /** The printer used to print string expressions */
  protected SExpPrinter _stringPrinter;

  public ConstraintPrinter() {
    _expPrinter = new IExpPrinter();
    _stringPrinter = new SExpPrinter();
  }

  public ConstraintPrinter(IExpPrinter e, SExpPrinter s) {
    _expPrinter = e;
    _stringPrinter = s;
  }

  /**
   * Returns a string representation of the given Constraint (using the other print method).
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final String print(Constraint e) {
    StringBuilder builder = new StringBuilder();
    print(e, builder);
    return builder.toString();
  }

  /**
   * This is the main public access function.  Call this to ensure that the given constraint is
   * printed to the given string builder.
   * 
   * To define your own ConstraintPrinter, you can either override this method directly -- in which
   * case there is no need to override any of the other methods in the class -- or override (some
   * of) the functions it calls directly, which are: printVar, printNegatedVar, printTruth,
   * printFalsehood, printGeq, printEquals, printDistinct, printConjunction, printDisjunction,
   * printNot, printIff, printEqS, printUneqS.
   */
  public void print(Constraint c, StringBuilder builder) {
    switch (c) {
      case BVar x: printVar(x, builder); break;
      case NBVar x: printNegatedVar(x, builder); break;
      case Truth t: printTruth(builder); break;
      case Falsehood f: printFalsehood(builder); break;
      case Geq0 g: printGeq(g, builder); break;
      case Is0 i: printEquals(i, builder); break;
      case Neq0 n: printDistinct(n, builder); break;
      case Conjunction j: printConjunction(j, builder); break;
      case Disjunction j: printDisjunction(j, builder); break;
      case Not n: printNot(n, builder); break;
      case Iff i: printIff(i, builder); break;
      case EqS e: printEqS(e, builder); break;
      case UneqS u: printUneqS(u, builder); break;
    }
  }

  /**
   * Override this function to change how boolean variables are printed (if print is left unmasked).
   * The default functionality is just to add the name to the string builder unmodified.
   */
  protected void printVar(BVar x, StringBuilder builder) {
    builder.append(x.queryName());
  }

  /**
   * Override this function to change how negations of boolean variables are printed (if print is left
   * unmasked).  The default functionality is just to add ! followed by the name to the string
   * builder.
   */
  protected void printNegatedVar(NBVar x, StringBuilder builder) {
    builder.append("!");
    builder.append(x.queryName());
  }

  /**
   * Override this function to change how the truth constant is printed (if print is left unmasked).
   * The default functionality is just to print "true".
   */
  protected void printTruth(StringBuilder builder) {
    builder.append("true");
  }

  /**
   * Override this function to change how the falsehood constant is printed (if print is left
   * unmasked).  The default functionality is just to print "false".
   */
  protected void printFalsehood(StringBuilder builder) {
    builder.append("false");
  }

  /**
   * Helper function for printGeq, printEquals and printDistinct: this takes main.queryExpression(),
   * splits it up into a positive and a negative side (using Addition::split), and prints
   * positive <symbol> negative to builder.
   */
  protected void printComparison(Comparison comp, String symbol, StringBuilder builder) {
    IntegerExpression main = comp.queryExpression();
    symbol = " " + symbol + " ";
    if (main instanceof Addition a) {
      Pair<IntegerExpression,IntegerExpression> pair = a.split();
      _expPrinter.print(pair.fst(), builder);
      builder.append(symbol);
      _expPrinter.print(pair.snd(), builder);
    }
    else {
      _expPrinter.print(main);
      builder.append(symbol);
      builder.append("0");
    }
  }

  /**
   * Override this function to change how Geq0 constraints are printed (if print is left unmasked).
   * The default functionality uses printComparison.
   */
  protected void printGeq(Geq0 constr, StringBuilder builder) {
    printComparison(constr, ">=", builder);
  }

  /**
   * Override this function to change how Is0 constraints are printed (if print is left unmasked).
   * The default functionality uses printComparison.
   */
  protected void printEquals(Is0 constr, StringBuilder builder) {
    printComparison(constr, "=", builder);
  }

  /**
   * Override this function to change how Neq0 constraints are printed (if print is left unmasked).
   * The default functionality uses printComparison.
   */
  protected void printDistinct(Neq0 constr, StringBuilder builder) {
    printComparison(constr, "#", builder);
  }

  /**
   * Helper function: this prints the given Constraint to the builder, either directly if it is a
   * constant or variable, or bracketed otherwise.
   */
  protected final void printBracketed(Constraint constr, StringBuilder builder) {
    switch (constr) {
      case BVar x: printVar(x, builder); break;
      case NBVar x: printNegatedVar(x, builder); break;
      case Truth t: printTruth(builder); break;
      case Falsehood f: printFalsehood(builder); break;
      default:
        builder.append("(");
        print(constr, builder);
        builder.append(")");
    }
  }

  /**
   * Override this function to change how conjunctions are printed (if print is left unmasked).
   * The default functionality prints elem1 and ... and elemn, where an element is bracketed if it
   * is not basic.
   */
  protected void printConjunction(Conjunction constr, StringBuilder builder) {
    if (constr.numChildren() == 0) builder.append("[true]");
    else {
      printBracketed(constr.queryChild(1), builder);
      for (int i = 2; i <= constr.numChildren(); i++) {
        builder.append(" and ");
        printBracketed(constr.queryChild(i), builder);
      }
    }
  }

  /**
   * Override this function to change how disjunctions are printed (if print is left unmasked).
   * The default functionality prints elem1 or ... or elemn, where an element is bracketed if it
   * is not basic.
   */
  protected void printDisjunction(Disjunction constr, StringBuilder builder) {
    if (constr.numChildren() == 0) builder.append("[false]");
    else {
      printBracketed(constr.queryChild(1), builder);
      for (int i = 2; i <= constr.numChildren(); i++) {
        builder.append(" or ");
        printBracketed(constr.queryChild(i), builder);
      }
    }
  }

  /**
   * Override this function to change how negations are printed (if print is left unmasked).
   * The default functionality prints not elem, where the element is bracketed if it is not basic.
   */
  protected void printNot(Not constr, StringBuilder builder) {
    builder.append("not ");
    printBracketed(constr.queryChild(), builder);
  }

  /**
   * Override this function to change how equivalences are printed (if print is left unmasked).
   * The default functionality prints left == right, where left and right are bracketed if they are
   * not basic.
   */
  protected void printIff(Iff i, StringBuilder builder) {
    printBracketed(i.queryLeft(), builder);
    builder.append(" == ");
    printBracketed(i.queryRight(), builder);
  }

  /**
   * Override this function to change how string equalities are printed (if print is left unmasked).
   * The default functionality prints left = right.
   */
  protected void printEqS(EqS e, StringBuilder builder) {
    _stringPrinter.print(e.queryLeft(), builder);
    builder.append(" = ");
    _stringPrinter.print(e.queryRight(), builder);
  }

  /**
   * Override this function to change how string equalities are printed (if print is left unmasked).
   * The default functionality prints left # right.
   */
  protected void printUneqS(UneqS u, StringBuilder builder) {
    _stringPrinter.print(u.queryLeft(), builder);
    builder.append(" # ");
    _stringPrinter.print(u.queryRight(), builder);
  }
}

