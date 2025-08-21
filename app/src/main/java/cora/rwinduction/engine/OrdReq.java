/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

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

import charlie.util.Pair;
import charlie.terms.replaceable.Renaming;
import charlie.terms.Term;
import charlie.terms.TheoryFactory;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;
import charlie.printer.PrinterFactory;

/**
 * A requirement that left ≻ right or left ≽ right under some condition.  Within the rewriting
 * induction process, ordering requirements are tracked to pass into a termination process.
 */
public class OrdReq implements PrintableObject {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;
  private boolean _strict;
  private Renaming _renaming;

  /**
   * Creates a strict requirement.
   *
   * WARNING: the renaming becomes the property of the OrdReq: it may be shared with other objects,
   * but should not be changed afterwards as doing so will also affect the OrdReq.
   */
  public OrdReq(Term left, Term right, Term constraint, Renaming renaming) {
    _lhs = left;
    _rhs = right;
    _constraint = constraint;
    _strict = true;
    _renaming = renaming.makeImmutable();
  }

  /**
   * Creates a strict or non-strict requirement.
   *
   * WARNING: the renaming becomes the property of the OrdReq: it should not be changed afterwards
   * as doing so will also affect the OrdReq.
   */
  public OrdReq(Term left, Term right, Term constraint, Renaming renaming,
                boolean strict) {
    _lhs = left;
    _rhs = right;
    _constraint = constraint;
    _strict = strict;
    _renaming = renaming.makeImmutable();
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

  /** Returns the (unmodifiable) renaming that determines how to print the present OrdReq. */
  public Renaming queryRenaming() {
    return _renaming;
  }

  /** Adds the current ordering requirement to the given printer. */
  public void print(Printer printer) {
    printer.add(printer.makePrintable(_lhs, _renaming),
                " ",
                _strict ? printer.symbSucc() : printer.symbSucceq(),
                " ",
                printer.makePrintable(_rhs, _renaming));
    if (!_constraint.equals(TheoryFactory.trueValue)) {
      printer.add(" | ", printer.makePrintable(_constraint, _renaming));
    }
  }

  /**
   * Only for debugging or testing purposes!
   * Use a Printer or OutputModule to properly print a Hypothesis.
   */
  public String toString() {
    Printer printer = PrinterFactory.createPrinterNotForUserOutput();
    print(printer);
    return printer.toString();
  }
}

