/**************************************************************************************************
 Copyright 2025 Cynthia Kop & Liye Guo

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.confluence;

import charlie.terms.Term;
import charlie.printer.PrintableObject;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;

/** Critical peaks for LCSTRSs. */
public record CriticalPeak(Term top, Term lhs, Term rhs, Term constraint)
    implements PrintableObject {
  /** Prints to the printer. */
  public void print(Printer printer) {
    var renaming = printer.generateUniqueNaming(top, lhs, rhs, constraint);
    /* ⟨top, lhs ≈ rhs */
    printer.add(
      printer.symbLangle(),
      Printer.makePrintable(top, renaming), ", ",
      Printer.makePrintable(lhs, renaming), " ",
      printer.symbApprox(), " ",
      Printer.makePrintable(rhs, renaming));
    /* | constraint */
    if (!constraint.isValue() || !constraint.toValue().getBool()) {
      printer.add(" | ", Printer.makePrintable(constraint, renaming));
    }
    /* ⟩ */
    printer.add(printer.symbRangle());
  }

  /** Only for testing and debugging. */
  public String toString() {
    var printer = PrinterFactory.createPrinterNotForUserOutput();
    print(printer);
    return printer.toString();
  }
}
