/**************************************************************************************************
 Copyright 2024-2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.io;

import java.util.ArrayList;
import java.util.List;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;

/**
 * An OutputModule is used to print Cora data to the user.  This class combines
 * charlie.printer.Printer with a PageBuilder, thus allowing Cora-structures to be printed within
 * paragraphs and tables.  As with the PageBuilder, an OutputModule can either be something that
 * stores its output internally for later building through toString(), or that prints to a
 * terminal directly (for example at every call to println).
 */
public class OutputModule {
  public enum Style { Plain, Unicode }

  private Printer _printer;
  private PageBuilder _page;
  private Style _style;
  private PageBuilder.Table _table;

  /**
   * Create an OutputModule where all components are expected to become the property of this
   * OutputModule.  The calling function should not change them afterwards.
   */
  public OutputModule(Printer printer, PageBuilder page, Style style) {
    _printer = printer;
    _page = page;
    _style = style;
    _table = null;
  }

  /**
   * Create an OutputModule with the given page (which is expected to become the property of this
   * OutputModule), and a printer based on the given style and trs.
   */
  public OutputModule(TRS trs, PageBuilder page, Style style) {
    _printer = switch (style) {
      case Plain -> PrinterFactory.createPlainPrinter(trs);
      case Unicode -> PrinterFactory.createUnicodePrinter(trs);
    };
    _page = page;
    _style = style;
    _table = null;
  }

  /** This creates a module with Plain style (pure text, no unicode, printing to a text page). */
  public static OutputModule createPlainModule(TRS trs) {
    return new OutputModule(PrinterFactory.createPlainPrinter(trs),
                            new TextPageBuilder(),
                            Style.Plain);
  }

  /** This creates a module with Unicode style (pure text, but unicode symbols are allowed). */
  public static OutputModule createUnicodeModule(TRS trs) {
    return new OutputModule(PrinterFactory.createUnicodePrinter(trs),
                            new TextPageBuilder(),
                            Style.Unicode);
  }

  /**
   * Like createUnicodeModule, but does not require a TRS.  This is only supplied for the sake of
   * unit testing, since terms may not be printed correctly (it is possible that variables and
   * function symbols end up with the same name).
   */
  public static OutputModule createUnitTestModule() {
    return new OutputModule(PrinterFactory.createPrinterNotForUserOutput(),
                            new TextPageBuilder(),
                            Style.Unicode);
  }

  /**
   * This returns the style used for printing anything in this OutputModule.  Objects printing to
   * an OutputModule may use swith on the style to decide on how to print something.
   *
   * It is possible that future extensions of OutputModule will support more styles.  Anything
   * printing to an OutputModule should support at least the Plain style, and if the OutputModule
   * uses an unknown style, default to that.
   *
   * (Note that for most purposes, using the designated codes and print methods should suffice.)
   */
  public Style queryStyle() {
    return _style;
  }

  /**
   * This returns the underlying Printer that output for the module is currently stored in.  Note
   * that the contents of the printer will typically be reset many times during the lifestyle of
   * the OutputModule; they do not represent the information that has been stored in the
   * OutputModule so far!
   */
  public Printer queryPrinter() {
    return _printer;
  }

  /**
   * This uses the underlying Printer to generate a Renaming that takes all the variables (and
   * meta-variables) in the given terms into account.
   */
  public final Renaming generateUniqueNaming(Term ...terms) {
    return _printer.queryTermPrinter().generateUniqueNaming(terms);
  }

  /**
   * This uses the underlying Printer to generate a Renaming that takes all the variables (and
   * meta-variables) in the given terms into account.
   */
  public final Renaming generateUniqueNaming(List<Term> terms) {
    return _printer.queryTermPrinter().generateUniqueNaming(terms);
  }

  /**
   * When printing, the OutputModule keeps track of paragraphs: if some text is printed and we are
   * not yet in a paragraph, a new paragraph is started.  It is ended on a newline, or when a (new)
   * list is started.
   *
   * This method returns whether we are currently inside a paragraph: some text has been printed,
   * but no newline yet.  Note that we cannot be both in a paragraph and in a table.
   */
  public boolean queryInParagraph() {
    return _table == null && !_printer.isEmpty();
  }

  /**
   * The core print method.  The given text is printed, and codes in it are parsed.  The following
   * codes should be supported in any implementation of OutputModule:
   *   %{ruleArrow}, %{typeArrow}, %{mapsto}, %{thickArrow}, %{longArrow}, %{downArrow},
   *   %{revRuleArrow}
   *   %{vdash}, %{Vdash}, %{forall}, %{exists}, %{and}, %{or}, %{not}, %{implies}
   *   %{emptyset}, %{union}, %{subterm}, %{subtermeq}, %{supterm}, %{suptermeq},
   *   %{sqSupset}, %{sqSupseteq}, %{succ}, %{succeq}, %{greater}, %{smaller}, %{geq}, %{leq},
   *   %{distinct}, %{approx},
   *   %{sharp}, %{bullet}, %{star},
   *   %{alpha}, %{beta}, %{gamma}, %{delta}, %{epsilon}, %{zeta}, %{eta}, %{theta}, %{iota},
   *   %{kappa}, %{lambda}, %{mu}, %{nu}, %{xi}, %{pi}, %{rho}, %{sigma}, %{tau}, %{phi}, %{chi},
   *   %{psi}, %{omega},
   * and most importantly:
   *   codes %a, in order, are replaced by a string representation of the object of the same
   *   index in the given list.  This is allowed only for objects of a class supported by the
   *   underlying printer.
   *
   * For example, print("%a %{ruleArrow} %a | %a", [a,b,c]) causes "a → b | c" to be printed if the
   * current style has set the code for %{ruleArrow} to →.
   */
  public void print(String text, Object ...objects) {
    ArrayList<Object> parts = new ArrayList<Object>();
    int start = 0;
    int objectIndex = 0;
    int nextCodeStart;
    while ((nextCodeStart = readUntilNextCode(text, start, parts)) != -1) {
      String code = readCode(text, nextCodeStart);
      start = nextCodeStart + code.length();
      if (code.equals("%a")) {
        if (objectIndex >= objects.length) {
          throw new IllegalPrintException("Encountered at least " + (objectIndex+1) +
            " occurrences of %a in a print, while only " + objects.length +
            " objects were given! (Text is " + text + ")");
        }
        else parts.add(objects[objectIndex++]);
      }
      else if (code.equals("%%")) parts.add("%");
      else parts.add(translateCode(code));
    }
    if (objectIndex != objects.length) {
      throw new IllegalPrintException("Encountered only " + objectIndex + " occurrences of %a " +
        "in a print, while " + objects.length + " objects were given! (Text is " + text + ")");
    }
    _printer.add(parts);
  }

  /**
   * Helper function for print: this finds the place where the next code starts, returns it, and
   * adds the part from start until the next code into parts.  If there is no next code, then -1
   * is returned instead, and the whole substring starting at start is stored in parts.
   */
  private int readUntilNextCode(String text, int start, ArrayList<Object> parts) {
    int ret = text.indexOf('%', start);
    if (ret == -1) parts.add(text.substring(start));
    else parts.add(text.substring(start, ret));
    return ret;
  }

  /**
   * Helper function for print: this reads the code starting at text[codeStart] and returns it.
   * It is given that text[codeStart] is a %, but it is not guaranteed that this is really shaped
   * like a code; if it is incorrect, then an IllegalPrintException is thrown instead.
   */
  private String readCode(String text, int codeStart) {
    if (codeStart < text.length() - 1) {
      if (text.charAt(codeStart + 1) == 'a') return "%a";
      if (text.charAt(codeStart + 1) == '%') return "%%";
      if (text.charAt(codeStart + 1) == '{') {
        int end = text.indexOf('}', codeStart);
        if (end != -1) return text.substring(codeStart, end + 1);
      }
    }
    throw new IllegalPrintException("Encountered % in print to OutputModule without a valid " +
      "code: " + text.substring(codeStart));
  }

  /**
   * Helper function for print: this maps each recognised code to the corresponding printer
   * symbol.  If the given symbol is not recognised, an IllegalPrintException is thrown.
   */
  private String translateCode(String code) {
    return switch (code) {
      case "%{ruleArrow}" -> _printer.symbRuleArrow();
      case "%{typeArrow}" -> _printer.symbTypeArrow();
      case "%{mapsto}" -> _printer.symbMapsto();
      case "%{thickArrow}" -> _printer.symbThickArrow();
      case "%{longArrow}" -> _printer.symbLongArrow();
      case "%{downArrow}" -> _printer.symbDownArrow();
      case "%{revRuleArrow}" -> _printer.symbRevRuleArrow();
      case "%{vdash}" -> _printer.symbVdash();
      case "%{Vdash}" -> _printer.symbVDash();
      case "%{forall}" -> _printer.symbForall();
      case "%{exists}" -> _printer.symbExists();
      case "%{and}" -> _printer.symbAnd();
      case "%{or}" -> _printer.symbOr();
      case "%{not}" -> _printer.symbNot();
      case "%{implies}" -> _printer.symbImplies();
      case "%{iff}" -> _printer.symbIff();
      case "%{emptyset}" -> _printer.symbEmptySet();
      case "%{union}" -> _printer.symbUnion();
      case "%{subterm}" -> _printer.symbSubterm();
      case "%{subtermeq}" -> _printer.symbSubtermeq();
      case "%{supterm}" -> _printer.symbSupterm();
      case "%{suptermeq}" -> _printer.symbSuptermeq();
      case "%{sqSupset}" -> _printer.symbSqSupset();
      case "%{sqSupseteq}" -> _printer.symbSqSupseteq();
      case "%{succ}" -> _printer.symbSucc();
      case "%{succeq}" -> _printer.symbSucceq();
      case "%{greater}" -> _printer.symbGreater();
      case "%{smaller}" -> _printer.symbSmaller();
      case "%{geq}" -> _printer.symbGeq();
      case "%{leq}" -> _printer.symbLeq();
      case "%{langle}" -> _printer.symbLangle();
      case "%{rangle}" -> _printer.symbRangle();
      case "%{distinct}" -> _printer.symbDistinct();
      case "%{approx}" -> _printer.symbApprox();
      case "%{sharp}" -> _printer.symbSharp();
      case "%{bullet}" -> _printer.symbBullet();
      case "%{star}" -> _printer.symbStar();
      case "%{alpha}" -> _printer.symbAlpha();
      case "%{beta}" -> _printer.symbBeta();
      case "%{gamma}" -> _printer.symbGamma();
      case "%{delta}" -> _printer.symbDelta();
      case "%{epsilon}" -> _printer.symbEpsilon();
      case "%{zeta}" -> _printer.symbZeta();
      case "%{eta}" -> _printer.symbEta();
      case "%{theta}" -> _printer.symbTheta();
      case "%{iota}" -> _printer.symbIota();
      case "%{kappa}" -> _printer.symbKappa();
      case "%{lambda}" -> _printer.symbLambda();
      case "%{mu}" -> _printer.symbMu();
      case "%{nu}" -> _printer.symbNu();
      case "%{xi}" -> _printer.symbXi();
      case "%{pi}" -> _printer.symbPi();
      case "%{rho}" -> _printer.symbRho();
      case "%{sigma}" -> _printer.symbSigma();
      case "%{tau}" -> _printer.symbTau();
      case "%{phi}" -> _printer.symbPhi();
      case "%{chi}" -> _printer.symbChi();
      case "%{psi}" -> _printer.symbPsi();
      case "%{omega}" -> _printer.symbOmega();
      default ->
        throw new IllegalPrintException("Encountered code " + code + " which is not recognised.");
    };
  }

  /**
   * If we are currently in paragraph mode, this function ends the current paragraph; subsequent
   * text will be in a new paragraph.
   *
   * If we are currently in a table, this function ends the current row; subsequent text will be
   * in the first column of a new row.
   *
   * If we are not in either, this function just creates an empty paragraph (so extra whitespace).
   */
  public void println() {
    if (_table != null) {
      if (!_printer.isEmpty() || !_table.rowStarted()) _table.addCell(_printer.toString());
      _table.endRow();
    }
    else _page.addParagraph(_printer.toString());
    _printer.clear();
  }

  /**
   * println(text, o1, ..., on); is just shorthand for:
   *   print(text, o1, ..., on);
   *   println();
   */
  public void println(String text, Object ...objects) {
    print(text, objects);
    println();
  }

  /**
   * This indicates that a new table should be started. If we are already inside a table, this ends
   * the current table and starts a new one.  If we are in a paragraph, that paragraph is ended too.
   *
   * When we start a table, the next time we print we are printing to the cell in the first row,
   * first column.  There is no need to use nextColumn() first (and in fact, doing so will skip a
   * cell).
   *
   * To go to a new cell, use nextColumn(), and then print to that.  To go to the next row, use
   * println(). (This also immediately allows you to print to the first column in that row.)
   * To end the table, use endTable().
   */
  public void startTable() {
    if (_table != null) endTable();
    if (!_printer.isEmpty()) println();
    _table = new PageBuilder.Table();
  }

  /**
   * When we are in a table, this ends the current cell and starts a new one (in the next column).
   * Subsequent prints will be to this column.
   * If we are not in a table, calling this function will cause an Error to be thrown.
   */
  public void nextColumn() {
    if (_table == null) {
      throw new IllegalPrintException("Called nextColumn when no table was started!");
    }
    _table.addCell(_printer.toString());
    _printer.clear();
  }

  /**
   * nextColumn(text, o1, ..., on); is just shorthand for: print(text, o1, ..., on); nextColumn();
   * That is, we print the given text in the CURRENT cell, and start a new cell in the current
   * table row.
   */
  public void nextColumn(String text, Object ...objects) {
    print(text, objects);
    nextColumn();
  }

  /** This ends the current table.  If no table is open, an error is thrown instead. */
  public void endTable() {
    if (_table == null) {
      throw new IllegalPrintException("Called endTable when no table was started!");
    }
    if (!_printer.isEmpty()) {
      _table.addCell(_printer.toString());
      _printer.clear();
    }
    _table.endRow();
    _page.addTable(_table);
    _table = null;
  }

  /** This prints the given set of rules in a table to the output module. */
  public void printRules(List<Rule> rules) {
    startTable();
    for (Rule rule : rules) {
      println("%a", rule);
    }
    endTable();
  }

  /** This prints the given TRS to the output module. */
  public void printTrs(TRS trs) {
    print("%a with ", trs.queryTrsKind());
    if (trs.querySchemeCount() == 0) println("no additional rule schemes:");
    else if (trs.querySchemeCount() == 1) println("only rule scheme " + trs.queryScheme(0) + ":");
    else {
      print("rule schemes ");
      for (int i = 0; i < trs.querySchemeCount() - 2; i++) print("%a, ", trs.queryScheme(i));
      print("%a and %a:", trs.queryScheme(trs.querySchemeCount() - 2).toString(),
                          trs.queryScheme(trs.querySchemeCount() - 1).toString());
    }
    startTable();
    nextColumn("Signature:");
    boolean printedAny = false;
    for (FunctionSymbol f : trs.queryAlphabet().getSymbols()) {
      if (printedAny) nextColumn(" ");
      else printedAny = true;
      nextColumn("%a", f.queryName());
      nextColumn("::");
      nextColumn("%a", f.queryType());
      if (trs.isPrivate(f)) nextColumn("(private)");
      println();
    }
    if (!printedAny) println("(empty)");
    endTable(); startTable();
    printedAny = false;
    nextColumn("Rules:");
    for (int i = 0; i < trs.queryRuleCount(); i++) {
      if (printedAny) nextColumn(" ");
      else printedAny = true;
      println("%a", trs.queryRule(i));
    }
    if (!printedAny) println("(empty)");
    endTable();
  }

  /**
   * This prints the current status of the OutputModule to StdOut.
   * Note: doing this has the side effect that everything is closed (e.g., paragraphs, tables).
   */
  public void printToStdout() {
    if (_table != null) endTable();
    if (!_printer.isEmpty()) println();
    System.out.print(_page.toString());
  }

  /**
   * This returns the current status of the *completed* paragraphs and tables.  Any text that has
   * been printed but not yet completed through println (in the case of a paragraph) or endTable
   * (in the case of a table) is not included.
   */
  public String toString() {
    return _page.toString();
  }
}
