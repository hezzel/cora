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

package cora.rwinduction.engine;

import charlie.exceptions.IndexingException;
import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.terms.TermPrinter;
import charlie.terms.TheoryFactory;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;
import charlie.printer.PrinterFactory;
import java.util.Set;

/**
 * The basic data structure representing equations: this is a tuple of a left-hand side, a
 * right-hand side, and a constraint.  Equations are immutable.
 */
public final class Equation {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;

  /** Creates the equation lhs ≈ rhs | constraint */
  public Equation(Term lhs, Term rhs, Term constraint) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = constraint;
  }

  /** Creates the equation lhs ≈ rhs | true */
  public Equation(Term lhs, Term rhs) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = TheoryFactory.createValue(true);
  }

  public Term getLhs() {
    return _lhs;
  }

  public Term getRhs() {
    return _rhs;
  }

  public Term getConstraint() {
    return _constraint;
  }

  public boolean isConstrained() {
    if (_constraint.toValue() == null) return true;
    return !_constraint.toValue().getBool();
  }

  /**
   * Returns the subterm at the given position, assuming that this is indeed a position of the
   * current term.  Otherwise, returns null.
   */
  public Term querySubterm(EquationPosition pos) {
    Term t = pos.querySide() == EquationPosition.Side.Left ? _lhs : _rhs;
    try { return t.querySubterm(pos.queryPosition()); }
    catch (IndexingException e) { return null; }
  }

  /**
   * Replaces the subterm at the given position, assuming that this is indeed a position of the
   * current term and the types match.  Otherwise, throws an appropriate RuntimeException.
   */
  public Equation replaceSubterm(EquationPosition pos, Term replacement) {
    return switch (pos.querySide()) {
      case EquationPosition.Side.Left -> {
        Term l = _lhs.replaceSubterm(pos.queryPosition(), replacement);
        yield new Equation(l, _rhs, _constraint);
      }
      case EquationPosition.Side.Right -> {
        Term r = _rhs.replaceSubterm(pos.queryPosition(), replacement);
        yield new Equation(_lhs, r, _constraint);
      }
    };
  }

  /**
   * This function prints the current equation to the given printer, using the given Renaming for
   * its variables (and meta-variables).  This is used by the print function in EquationContext
   * and Hypothesis, and also by makePrintableWith.
   */
  void printWithRenaming(Printer printer, Renaming renaming) {
    printer.add(printer.makePrintable(_lhs, renaming),
                " ",
                printer.symbApprox(),
                " ",
                printer.makePrintable(_rhs, renaming));
    if (isConstrained()) printer.add(" | ", printer.makePrintable(_constraint, renaming));
  }

  /**
   * An Equation cannot be directly printed to a Printer or OutputModule, because Equations should
   * always be coupled with a specific variable naming.  If such a Renaming is given, then
   * equation.makePrintableObject(renaming) *can* be printed as usual.
   */
  public PrintableObject makePrintableWith(Renaming renaming) {
    return new PrintableObject() {
      public void print(Printer printer) {
        printWithRenaming(printer, renaming);
      }
    };
  }

  /*
   * Only for debugging or testing purposes!
   * To properly print an Equation, add makePrintableWith(renaming) to a Printer or OutputModuel,
   * where renaming is an appropriate renaming.  (Note that equations should typically be printed
   * with the same Renaming throughout the proof process).
   */
  public String toString() {
    Printer printer = PrinterFactory.createPrinterNotForUserOutput();
    printer.add(_lhs, " ", printer.symbApprox(), " ", _rhs, " | ", _constraint);
    return printer.toString();
  }
}
