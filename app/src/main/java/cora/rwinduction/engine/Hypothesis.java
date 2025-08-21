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

import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;
import charlie.printer.PrinterFactory;

/**
 * A Hypothesis couples an Equation with a Renaming and an index.
 * All hypotheses are immutable.
 */
public class Hypothesis implements PrintableObject {
  private Equation _equation;
  private Renaming _varNaming;
  private int _index;

  /**
   * Creates the hypothesis.
   *
   * WARNING: the naring becomes the property of the current Hypothesis ,so should in principle be
   * created for it, or already be immutable!  If modifiable, it may not be modified by some other
   * class afterwards.
   */
  public Hypothesis(Equation equation, int index, Renaming naming) {
    _equation = equation;
    _index = index;
    _varNaming = naming.makeImmutable();
  }

  /** Returns the underlying equation. */
  public Equation getEquation() {
    return _equation;
  }

  /** Returns the index this hypothesis has within the proof. */
  public int getIndex() {
    return _index;
  }

  /** Returns the name of this hypothesis within the proof. */
  public String getName() {
    return "H" + getIndex();
  }

  /** Returns the (unmodifiable) Renaming that determines how to print the equation. */
  public Renaming getRenaming() {
    return _varNaming;
  }

  /** Adds the current hypothesis to the given printer. */
  public void print(Printer printer) {
    printer.add(getName(), ": ");
    _equation.printWithRenaming(printer, _varNaming);
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

