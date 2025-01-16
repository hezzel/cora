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

package cora.io;

import java.util.Set;
import java.util.ArrayList;
import java.util.Collections;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.types.TypePrinter;
import charlie.terms.position.Position;
import charlie.terms.position.PositionPrinter;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;
import charlie.printer.PlainTypePrinter;
import charlie.printer.PlainTermPrinter;
import charlie.printer.PlainPositionPrinter;

public class DefaultOutputModule implements OutputModule {
  private TypePrinter _typePrinter;
  private PositionPrinter _positionPrinter;
  private TermPrinter _termPrinter;
  private Style _style;
  private StringBuilder _builder;
  private boolean _inParagraph;
  private ArrayList< ArrayList<String> > _currentTable;
  private ArrayList< Pair<String,String> > _codes;

  /** This creates a module with Plain style (pure text, no unicode). */
  public static OutputModule createPlainModule(TRS trs) {
    TypePrinter typr = new PlainTypePrinter();
    PositionPrinter popr = new PlainPositionPrinter();
    Set<String> avoid = trs == null ? Set.of() : trs.queryFunctionSymbolNames();
    ArrayList<Pair<String,String>> codes = new ArrayList<Pair<String,String>>();
    codes.add(new Pair<String,String>("%{ruleArrow}", "->"));
    codes.add(new Pair<String,String>("%{typeArrow}", "->"));
    codes.add(new Pair<String,String>("%{mapsto}", "|->"));
    codes.add(new Pair<String,String>("%{thickArrow}", "=>"));
    codes.add(new Pair<String,String>("%{longArrow}", "-->"));
    codes.add(new Pair<String,String>("%{downArrow}", "!down"));
    codes.add(new Pair<String,String>("%{revRuleArrow}", "<-"));
    codes.add(new Pair<String,String>("%{vdash}", "|-"));
    codes.add(new Pair<String,String>("%{Vdash}", "|="));
    codes.add(new Pair<String,String>("%{forall}", "FORALL"));
    codes.add(new Pair<String,String>("%{exists}", "EXISTS"));
    codes.add(new Pair<String,String>("%{emptyset}", "{}"));
    codes.add(new Pair<String,String>("%{sqsupset}", "[>]"));
    codes.add(new Pair<String,String>("%{sqsupseteq}", "[>=]"));
    codes.add(new Pair<String,String>("%{succ}", "(>)"));
    codes.add(new Pair<String,String>("%{succeq}", "(>=)"));
    codes.add(new Pair<String,String>("%{subterm}", "|<|"));
    codes.add(new Pair<String,String>("%{subtermeq}", "|<=|"));
    codes.add(new Pair<String,String>("%{supterm}", "|>|"));
    codes.add(new Pair<String,String>("%{suptermeq}", "|>=|"));
    codes.add(new Pair<String,String>("%{union}", "UNION"));
    codes.add(new Pair<String,String>("%{greater}", ">"));
    codes.add(new Pair<String,String>("%{smaller}", "<"));
    codes.add(new Pair<String,String>("%{geq}", ">="));
    codes.add(new Pair<String,String>("%{leq}", "<="));
    codes.add(new Pair<String,String>("%{and}", "/\\"));
    codes.add(new Pair<String,String>("%{or}", "\\/"));
    codes.add(new Pair<String,String>("%{not}", "not "));
    codes.add(new Pair<String,String>("%{implies}", "=>"));
    codes.add(new Pair<String,String>("%{distinct}", "!="));
    codes.add(new Pair<String,String>("%{approx}", "-><-"));
    codes.add(new Pair<String,String>("%{bullet}", "#"));
    codes.add(new Pair<String,String>("%{alpha}", "alpha"));
    codes.add(new Pair<String,String>("%{beta}", "beta"));
    codes.add(new Pair<String,String>("%{gamma}", "gamma"));
    codes.add(new Pair<String,String>("%{delta}", "delta"));
    codes.add(new Pair<String,String>("%{epsilon}", "eps"));
    codes.add(new Pair<String,String>("%{zeta}", "zeta"));
    codes.add(new Pair<String,String>("%{eta}", "eta"));
    codes.add(new Pair<String,String>("%{theta}", "th"));
    codes.add(new Pair<String,String>("%{iota}", "iota"));
    codes.add(new Pair<String,String>("%{kappa}", "kappa"));
    codes.add(new Pair<String,String>("%{lambda}", "\\"));
    codes.add(new Pair<String,String>("%{mu}", "mu"));
    codes.add(new Pair<String,String>("%{nu}", "nu"));
    codes.add(new Pair<String,String>("%{xi}", "xi"));
    codes.add(new Pair<String,String>("%{pi}", "pi"));
    codes.add(new Pair<String,String>("%{rho}", "rho"));
    codes.add(new Pair<String,String>("%{sigma}", "sigma"));
    codes.add(new Pair<String,String>("%{tau}", "tau"));
    codes.add(new Pair<String,String>("%{phi}", "phi"));
    codes.add(new Pair<String,String>("%{chi}", "chi"));
    codes.add(new Pair<String,String>("%{psi}", "psi"));
    codes.add(new Pair<String,String>("%{omega}", "omega"));
    return new DefaultOutputModule(typr, popr, new PlainTermPrinter(avoid), Style.Plain, codes);
  }

  /**
   * Like createPlainModule, but does not require a TRS.  Note that this means that terms may not
   * be printed correctly (it is possible that variables and function symbols end up with the same
   * name).
   */
  public static OutputModule createPlainModule() { return createPlainModule(null); }

  /** This creates a module with Unicode style (pure text, but unicode symbols are allowed). */
  public static OutputModule createUnicodeModule(TRS trs) {
    TypePrinter typr = new TypePrinter();
    PositionPrinter popr = new PositionPrinter();
    Set<String> avoid = trs == null ? Set.of() : trs.queryFunctionSymbolNames();
    ArrayList<Pair<String,String>> codes = new ArrayList<Pair<String,String>>();
    codes.add(new Pair<String,String>("%{ruleArrow}", "→"));
    codes.add(new Pair<String,String>("%{typeArrow}", "→"));
    codes.add(new Pair<String,String>("%{mapsto}", "↦"));
    codes.add(new Pair<String,String>("%{thickArrow}", "➡"));
    codes.add(new Pair<String,String>("%{longArrow}", "⟶"));
    codes.add(new Pair<String,String>("%{downArrow}", "↓"));
    codes.add(new Pair<String,String>("%{revRuleArrow}", "←"));
    codes.add(new Pair<String,String>("%{vdash}", "⊢"));
    codes.add(new Pair<String,String>("%{Vdash}", "⊨"));
    codes.add(new Pair<String,String>("%{forall}", "∀"));
    codes.add(new Pair<String,String>("%{exists}", "∃"));
    codes.add(new Pair<String,String>("%{emptyset}", "ø"));
    codes.add(new Pair<String,String>("%{sqsupset}", "⊐"));
    codes.add(new Pair<String,String>("%{sqsupseteq}", "⊒"));
    codes.add(new Pair<String,String>("%{succ}", "≻"));
    codes.add(new Pair<String,String>("%{succeq}", "≽"));
    codes.add(new Pair<String,String>("%{subterm}", "⊲"));
    codes.add(new Pair<String,String>("%{subtermeq}", "⊴"));
    codes.add(new Pair<String,String>("%{supterm}", "⊳"));
    codes.add(new Pair<String,String>("%{suptermeq}", "⊵"));
    codes.add(new Pair<String,String>("%{union}", "∪"));
    codes.add(new Pair<String,String>("%{greater}", ">"));
    codes.add(new Pair<String,String>("%{smaller}", "<"));
    codes.add(new Pair<String,String>("%{geq}", "≥"));
    codes.add(new Pair<String,String>("%{leq}", "≤"));
    codes.add(new Pair<String,String>("%{and}", "∧"));
    codes.add(new Pair<String,String>("%{or}", "∨"));
    codes.add(new Pair<String,String>("%{not}", "¬"));
    codes.add(new Pair<String,String>("%{implies}", "⇒"));
    codes.add(new Pair<String,String>("%{distinct}", "≠"));
    codes.add(new Pair<String,String>("%{approx}", "≈"));
    codes.add(new Pair<String,String>("%{bullet}", "•"));
    codes.add(new Pair<String,String>("%{alpha}", "α"));
    codes.add(new Pair<String,String>("%{beta}", "β"));
    codes.add(new Pair<String,String>("%{gamma}", "γ"));
    codes.add(new Pair<String,String>("%{delta}", "δ"));
    codes.add(new Pair<String,String>("%{epsilon}", "ε"));
    codes.add(new Pair<String,String>("%{zeta}", "ζ"));
    codes.add(new Pair<String,String>("%{eta}", "η"));
    codes.add(new Pair<String,String>("%{theta}", "θ"));
    codes.add(new Pair<String,String>("%{iota}", "ι"));
    codes.add(new Pair<String,String>("%{kappa}", "κ"));
    codes.add(new Pair<String,String>("%{lambda}", "λ"));
    codes.add(new Pair<String,String>("%{mu}", "μ"));
    codes.add(new Pair<String,String>("%{nu}", "ν"));
    codes.add(new Pair<String,String>("%{xi}", "ξ"));
    codes.add(new Pair<String,String>("%{pi}", "π"));
    codes.add(new Pair<String,String>("%{rho}", "ρ"));
    codes.add(new Pair<String,String>("%{sigma}", "σ"));
    codes.add(new Pair<String,String>("%{tau}", "τ"));
    codes.add(new Pair<String,String>("%{phi}", "φ"));
    codes.add(new Pair<String,String>("%{chi}", "χ"));
    codes.add(new Pair<String,String>("%{psi}", "ψ"));
    codes.add(new Pair<String,String>("%{omega}", "ω"));
    return new DefaultOutputModule(typr, popr, new TermPrinter(avoid), Style.Unicode, codes);
  }

  /**
   * Like createUnicodeModule, but does not require a TRS.  Note that this means that terms may not
   * be printed correctly (it is possible that variables and function symbols end up with the same
   * name).
   */
  public static OutputModule createUnicodeModule() { return createUnicodeModule(null); }

  /** This creates a standard module for printing. */
  public static OutputModule createDefaultModule(TRS trs) {
    return createUnicodeModule(trs);
  }

  /**
   * Like createDefaultModule, but does not require a TRS.  Note that this means that terms may not
   * be printed correctly (it is possible that variables and function symbols end up with the same
   * name).
   */
  public static OutputModule createDefaultModule() { return createDefaultModule(null); }

  private DefaultOutputModule(TypePrinter types, PositionPrinter posses, TermPrinter terms,
                              Style style, ArrayList<Pair<String,String>> codes) {
    _typePrinter = types;
    _positionPrinter = posses;
    _termPrinter = terms;
    _style = style;
    _codes = codes;
    _builder = new StringBuilder();
    _inParagraph = false;
    _currentTable = null;
  }

  @Override
  public void clear() { _builder = new StringBuilder(); }

  @Override
  public TypePrinter queryTypePrinter() { return _typePrinter; }

  @Override
  public PositionPrinter queryPositionPrinter() { return _positionPrinter; }

  @Override
  public TermPrinter queryTermPrinter() { return _termPrinter; }

  @Override
  public Style queryStyle() { return _style; }

  @Override
  public boolean queryInParagraph() { return _inParagraph; }

  public boolean inTable() { return _currentTable != null; }

  /** Starts a table.  If we were already in a table, it is ended first, and a new one begun. */
  @Override
  public void startTable() {
    if (_inParagraph) println();
    if (_currentTable != null) endTable();
    _currentTable = new ArrayList< ArrayList<String> >();
    _currentTable.add(new ArrayList<String>());
  }

  /** Adds the given concrete text to the current cell we're writing to in the table. */
  private void addToCurrentCell(String txt) {
    ArrayList<String> myrow = _currentTable.get(_currentTable.size()-1);
    if (myrow.size() == 0) myrow.add(txt);
    else myrow.set(myrow.size()-1, myrow.get(myrow.size()-1) + txt);
  }

  /** This ends the current cell, so subsequent prints write to the next. */
  @Override
  public void nextColumn() {
    if (_currentTable == null) {
      throw new IllegalPrintException("Called endTable when no table was started!");
    }
    ArrayList<String> myrow = _currentTable.get(_currentTable.size()-1);
    if (myrow.size() == 0) myrow.add("");
    myrow.add("");
  }

  /** Helper function for endTable: returns the length each column in _currentTable should have. */
  private ArrayList<Integer> getColumnSizes() {
    // find the greatest number of columns in the current table
    int numCols = 1;
    for (int i = 0; i < _currentTable.size(); i++) {
      if (_currentTable.get(i).size() > numCols) numCols = _currentTable.get(i).size();
    }
    // find the length each column should have
    ArrayList<Integer> ret = new ArrayList<Integer>();
    for (int col = 0; col < numCols; col++) ret.add(0);
    for (int row = 0; row < _currentTable.size(); row++) {
      ArrayList<String> cells = _currentTable.get(row);
      for (int col = 0; col < cells.size(); col++) {
        if (cells.get(col).length() > ret.get(col)) ret.set(col, cells.get(col).length());
      }
    }
    return ret;
  }

  /**
   * This ends the current table: it ends the column and row if necessary, computes the respective
   * sizes of all the cells, uses this to determine the overall lay-out of the table, and then
   * prints the whole table to the internal string builder.
   */
  @Override
  public void endTable() {
    if (_currentTable == null) {
      throw new IllegalPrintException("Called endTable when no table was started!");
    }
    // if there's an empty line at the end of the table, we remove it
    if (_currentTable.size() > 0 && _currentTable.get(_currentTable.size()-1).size() == 0) {
      _currentTable.remove(_currentTable.size()-1);
    }
    // print the table, taking the width of all columns into account
    ArrayList<Integer> width = getColumnSizes();
    for (int row = 0; row < _currentTable.size(); row++) {
      _builder.append("  ");  // indent
      ArrayList<String> cells = _currentTable.get(row);
      while (cells.size() > 0 && cells.get(cells.size()-1).equals("")) cells.remove(cells.size()-1);
      for (int col = 0; col < cells.size()-1; col++) {
        _builder.append(String.format("%-" + (width.get(col)+1) + "s", cells.get(col)));
      }
      if (cells.size() > 0) _builder.append(cells.get(cells.size()-1));
      _builder.append("\n");
    }
    _builder.append("\n");
    _currentTable = null;
  }

  /**
   * This handles the ending of a line, which does very different things depending on whether we are
   * in a paragraph or in a table.
   */
  @Override
  public void println() {
    if (_inParagraph) {
      _inParagraph = false;
      _builder.append("\n\n");
    }
    else if (_currentTable == null) _builder.append("\n");
    else {
      if (_currentTable.size() == 0 || _currentTable.get(_currentTable.size()-1).size() == 0) {
        addToCurrentCell("");
      }
      _currentTable.add(new ArrayList<String>());
    }
  }

  /**
   * The core printing functionality, printing to either a paragraph of the current cell in the
   * table.
   */
  @Override
  public void print(String text, Object ...objects) {
    String txt = makeString(text, objects);
    if (!_inParagraph && _currentTable == null) _inParagraph = true;
    if (_inParagraph) _builder.append(txt);
    else addToCurrentCell(txt);
  }

  /** This prints the results so far to standard out. */
  @Override
  public void printToStdout() {
    System.out.print(toString());
  }

  /** This returns a string representation of the results so far. */
  public String toString() {
    return _builder.toString();
  }

  /**
   * This function handles the primary functionality of print: printing the given text to a string,
   * taking into account the codes and arguments.
   */
  private String makeString(String text, Object[] objects) {
    text = replaceCodes(text);
    if (objects.length == 0) return text;
    while (objects.length == 1 && objects[0] instanceof Object[]) objects = (Object[])objects[0];
    makeRenaming(objects);
    StringBuilder ret = new StringBuilder();
    int searchfrom = 0;
    for (int i = 0; i < objects.length; i++) {
      int pos = text.indexOf("%a", searchfrom);
      if (pos < 0) {
        throw new IllegalPrintException("Illegal print; arguments " + text + " with " +
                                        objects.length + " arguments");
      }
      ret.append(text.substring(searchfrom, pos));
      ret.append(printObject(objects[i]));
      searchfrom = pos + 2;
    }
    if (searchfrom < text.length()) ret.append(text.substring(searchfrom));
    return ret.toString();
  }

  /**
   * This helper function for makeString uses _codes to replace all the known codes in the given
   * text.
   */
  private String replaceCodes(String text) {
    for (int i = 0; i < _codes.size(); i++) {
      text = text.replace(_codes.get(i).fst(), _codes.get(i).snd());
    }
    return text;
  }

  /**
   * This helper function for makeString finds a renaming for all the terms in the given object
   * list, and updates the list to make the terms include the renaming.
   */
  private void makeRenaming(Object[] objects) {
    ArrayList<Term> terms = new ArrayList<Term>();
    for (int i = 0; i < objects.length; i++) {
      if (objects[i] instanceof Term t) terms.add(t);
    }
    Renaming renaming = _termPrinter.generateUniqueNaming(terms);
    for (int i = 0; i < objects.length; i++) {
      if (objects[i] instanceof Term t) objects[i] = new Pair<Term,Renaming>(t, renaming);
    }
  }

  /**
   * This helper function for makeString prints the given object as it should be printed, if it is
   * a known object type.  If the object does not have a recognised type, then its toString() is
   * used.
   */
  private String printObject(Object ob) {
    if (ob instanceof Type y) return _typePrinter.print(y);
    if (ob instanceof Position p) return _positionPrinter.print(p);
    if (ob instanceof Rule r) return printRule(r, null);
    // no need to special-case Terms, as these have all been transformed into Pairs
    if (ob instanceof Pair p) {
      if (p.fst() instanceof Term t && p.snd() instanceof Renaming renaming) {
        return _termPrinter.print(t, renaming);
      }
      if (p.fst() instanceof String s && p.snd() instanceof Object[] obs) {
        return makeString(s, obs);
      }
      if (p.fst() instanceof String s) {
        return makeString(s, new Object[] { p.snd() });
      }
      if (p.fst() instanceof Rule rho && p.snd() instanceof Renaming renaming) {
        return printRule(rho, renaming);
      }
      if (p.fst() instanceof Substitution subst) {
        if (p.snd() instanceof Renaming ren) return printSubstitution(subst, ren, ren);
        if (p.snd() instanceof Pair p2 && p2.fst() instanceof Renaming ren1 &&
                                          p2.snd() instanceof Renaming ren2) {
          return printSubstitution(subst, ren1, ren2);
        }
      }
    }
    return ob.toString();
  }

  /** Helper function for printObject: replaces a rule by a Pair<Rule,Renaming>. */
  private Object generateRuleNaming(Rule r) {
    Renaming ren = _termPrinter.generateUniqueNaming(r.queryLeftSide(), r.queryRightSide(),
                                                     r.queryConstraint());
    return new Pair<Rule,Renaming>(r, ren);
  }

  /**
   * Helper function for printObject: determines a string representation for the given rule, along
   * with the given renaming.  If the renaming is null, then a suitable renaming will be generated.
   */
  private String printRule(Rule rho, Renaming renaming) {
    if (renaming == null) {
      renaming = _termPrinter.generateUniqueNaming(rho.queryLeftSide(), rho.queryRightSide(),
                                                   rho.queryConstraint());
    }
    StringBuilder ret = new StringBuilder();
    _termPrinter.print(rho.queryLeftSide(), renaming, ret);
    ret.append(replaceCodes(" %{ruleArrow} "));
    _termPrinter.print(rho.queryRightSide(), renaming, ret);
    if (rho.isConstrained()) {
      ret.append(" | ");
      _termPrinter.print(rho.queryConstraint(), renaming, ret);
    }
    return ret.toString();
  }

  /**
   * Helper function for printSubstitution: this creates a string representation for the
   * substitution, with (meta-)variable names for the domain taken from keyNaming, and the names
   * for the values taken from valueNaming.
   */
  private String printSubstitution(Substitution gamma, Renaming keyNaming, Renaming valueNaming) {
    // put the names in a list, so we can order them
    ArrayList<Pair<Replaceable,String>> dom = new ArrayList<Pair<Replaceable,String>>();
    for (Replaceable x : gamma.domain()) {
      String xname = keyNaming.getName(x);
      if (xname == null) {
        throw new IllegalArgumentException("KeyNaming given to printSubstitution does not have " +
          "a mapping for " + x.queryName() + ".");
      }
      dom.add(new Pair<Replaceable,String>(x, xname));
    }
    Collections.sort(dom, (x,y) ->
      x.fst().queryReplaceableKind() == y.fst().queryReplaceableKind() ? x.snd().compareTo(y.snd())
                                : x.fst().queryReplaceableKind() - y.fst().queryReplaceableKind());

    // print the lot
    StringBuilder ret = new StringBuilder("[");
    for (int i = 0; i < dom.size(); i++) {
      if (i > 0) ret.append(", ");
      ret.append(dom.get(i).snd());
      ret.append(" := ");
      _termPrinter.print(gamma.get(dom.get(i).fst()), valueNaming, ret);
    }
    ret.append("]");
    return ret.toString();
  }

  @Override
  public void printTrs(TRS trs) {
    print("%a with ", trs.queryTrsKind());
    if (trs.querySchemeCount() == 0) println("no additional rule schemes:");
    else if (trs.querySchemeCount() == 1) println("only rule scheme " + trs.queryScheme(0) + ":");
    else {
      print("rule schemes ");
      for (int i = 0; i < trs.querySchemeCount() - 2; i++) print("%a, ", trs.queryScheme(i));
      print("%a and %a:", trs.queryScheme(trs.querySchemeCount() - 2),
                          trs.queryScheme(trs.querySchemeCount() - 1));
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
}
