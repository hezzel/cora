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

import java.util.List;
import charlie.terms.TermPrinter;
import charlie.trs.Rule;
import charlie.trs.TRS;

/**
 * An OutputModule is used to print Cora data to the user.  This class is meant to be implemented
 * to allow output to be printed in a variety of ways; for example, plain, unicode and HTML output.
 *
 * It is also possible to define extensions of an existing OutputModule that know how to print
 * special kinds of objects (e.g., dependency pairs, equations).  This is handled using the
 * OutputModuleAdapter.
 */
public interface OutputModule {
  enum Style { Plain, Unicode }

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
  Style queryStyle();

  /**
   * This returns the TermPrinter used for printing terms in this OutputModule.  It can also be
   * used to generate Renamings.
   */
  TermPrinter queryTermPrinter();

  /**
   * When printing, the OutputModule keeps track of paragraphs: if some text is printed and we are
   * not yet in a paragraph, a new paragraph is started.  It is ended on a newline, or when a (new)
   * list is started.
   *
   * This method returns whether we are currently inside a paragraph: some text has been printed,
   * but no newline yet.  Note that we cannot be both in a paragraph and in a table.
   */
  boolean queryInParagraph();

  /**
   * The core print method.  The given text is printed, and codes in it are parsed.  The following
   * codes should be supported in any implementation of OutputModule:
   *   %{ruleArrow}, %{typeArrow}, %{mapsto}, %{thickArrow}, %{longArrow}, %{downArrow},
   *   %{revRuleArrow}
   *   %{vdash}, %{Vdash}, %{forall}, %{exists}, %{emptyset},
   *   %{sqSupset}, %{sqSupseteq}, %{succ}, %{succeq},
   *   %{subterm}, %{subtermeq}, %{supterm}, %{suptermeq},
   *   %{greater}, %{smaller}, %{geq}, %{leq}, %{and}, %{or}, %{not}, %{implies}, %{distinct},
   *   %{alpha}, %{beta}, %{gamma}, %{delta}, %{epsilon}, %{zeta}, %{eta}, %{theta}, %{iota},
   *   %{kappa}, %{lambda}, %{mu}, %{nu}, %{xi}, %{pi}, %{rho}, %{sigma}, %{tau}, %{phi}, %{chi},
   *   %{psi}, %{omega},
   * and most importantly:
   *   codes %a, in order, are replaced by a string representation of the object of the same
   *   index in the given list.
   *
   * Special behaviour is defined for %a for Type, Term and Rule bbjects, as well as
   * Pair<Term,Renaming> and Pair<String,Object[]> objects; all other objects are printed through
   * ob.toString() (although it is possible for extensions of OutputModule to define their own
   * improved ways of printing other kinds of objects).
   *
   * In particular, the Term objects are printed in such a way that occurrences of the same
   * variables in multiple terms (in the given object list) are all printed with the same name,
   * and this name is only used for ONE variable.  (Formally: they are printed using the same
   * naming: TermPrinter.Renaming.)
   *
   * For example, print("%a %{ruleArrow} %a | %a", [a,b,c]) causes"a → b | c" to be printed if the
   * current style has set the code for %{ruleArrow} to →.
   *
   * Note: if you pass a Pair<Term,Renaming> as one of the Object arguments instead of just a term,
   * then this will lead to the given term being printed with the given Renaming, and not being
   * considered for the naming of other terms in the given list.  Hence, if there is a need to
   * print terms across multiple paragraphs using the same Renaming, then the calling method can
   * use this to do so (but needs to keep track of the Renaming by itself).  The same works for a
   * Pair<Rule,Renaming>.
   *
   * Note also: if you pass a Pair<String,Object[]> as one of the Object arguments (say (s,lst)),
   * that's the same as calling print(s, lst).
   */
  void print(String text, Object ...objects);

  /**
   * If we are currently in paragraph mode, this function ends the current paragraph; subsequent
   * text will be in a new paragraph.
   *
   * If we are currently in a table, this function ends the current row; subsequent text will be
   * in the first column of a new row.
   *
   * If we are not in either, this function just creates an empty paragraph (so extra whitespace).
   */
  void println();

  /**
   * println(text, o1, ..., on); is just shorthand for:
   *   print(text, o1, ..., on);
   *   println();
   */
  default void println(String text, Object ...objects) {
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
  void startTable();

  /**
   * When we are in a table, this ends the current cell and starts a new one (in the next column).
   * Subsequent prints will be to this column.
   * If we are not in a table, calling this function will cause an Error to be thrown.
   */
  void nextColumn();

  /**
   * nextColumn(text, o1, ..., on); is just shorthand for: print(text, o1, ..., on); nextColumn();
   * That is, we print the given text in the CURRENT cell, and start a new cell in the current
   * table row.
   */
  default void nextColumn(String text, Object ...objects) {
    print(text, objects);
    nextColumn();
  }

  /** This ends the current table.  If no table is open, an error is thrown instead. */
  void endTable();

  /** This prints the given set of rules in a table to the output module. */
  default void printRules(List<Rule> rules) {
    startTable();
    for (Rule rule : rules) { println("%a", rule); }
    endTable();
  }

  /**
   * Clear the contents of the output module.
   */
  void clear();

  /** This prints the given TRS to the output module. */
  void printTrs(TRS trs);

  /**
   * This prints the current status of the OutputModule to StdOut.
   * Note: doing this has the side effect that everything is closed (e.g., paragraphs, tables).
   * The same holds if toString() is called.
   */
  void printToStdout();
}
