/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.printer;

import java.util.Set;
import charlie.types.TypePrinter;
import charlie.terms.position.PositionPrinter;
import charlie.terms.TermPrinter;
import charlie.trs.TRS;

public class PrinterFactory {
  /** This creates a printer with Unicode style (pure text, but unicode symbols are allowed). */
  public static Printer createUnicodePrinter(TRS trs) {
    TypePrinter ty = new TypePrinter();
    PositionPrinter po = new PositionPrinter();
    TermPrinter te = new TermPrinter(trs.queryFunctionSymbolNames());
    return new UnicodePrinter(ty, po, te);
  }

  /** This creates a printer with Plain style (pure text, no unicode). */
  public static Printer createPlainPrinter(TRS trs) {
    TypePrinter ty = new PlainTypePrinter();
    PositionPrinter po = new PlainPositionPrinter();
    TermPrinter te = new PlainTermPrinter(trs.queryFunctionSymbolNames());
    return new AsciiPrinter(ty, po, te);
  }

  /** This creates a printer with plain output that is designed to be parsed. */
  public static Printer createParseablePrinter(TRS trs) {
    TypePrinter ty = new PlainTypePrinter();
    PositionPrinter po = new PlainPositionPrinter();
    TermPrinter te = new ParseableTermPrinter(trs.queryFunctionSymbolNames());
    return new ParseablePrinter(ty, po, te);
  }

  /**
   * This creates a printer with Unicode style, and without taking any forbidden symbols into
   * account for the TermPrinter.  This is not meant for user output (where the TermPrinter really
   * should avoid naming variables the same as function symbols), but is useful for unit testing and
   * toString() functions whose output may be used for instance by the IDE, but is not meant for
   * showing to the user.
   */
  public static Printer createPrinterNotForUserOutput() {
    return new UnicodePrinter(new TypePrinter(), new PositionPrinter(), new TermPrinter(Set.of()));
  }

  /**
   * This creates a plain Printer, where term printing by default shows variable indexes rather
   * than a more prettified naming.  (A given varnaming is still respected, but any Renaming
   * generated using this printer will show indexes.)
   */
  public static Printer createDebugPrinter() {
    return new AsciiPrinter(new PlainTypePrinter(), new PlainPositionPrinter(),
                            new DebugTermPrinter());
  }
}

