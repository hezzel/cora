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
import cora.terms.TermPrinter;
import cora.trs.Rule;

/**
 * An OutputModule is used to print Cora data to the user.  This class is meant to be implemented
 * to allow output to be printed in a variety of ways; for example, plain, unicode and HTML output.
 *
 * To support this, and also to support the broad spectrum of things that should be printable, the
 * OutputModule is in principle implemented through the Adapter pattern: there is a default
 * version, and extensions may for instance define additional codes for the print function.
 */
public interface OutputModule {
  enum Style { Plain, Unicode }

  /**
   * This returns the style used for printing anything in this OutputModule.  Objects printing to
   * an OutputModule may use swith on the style to decide on how to print something (for example,
   * whether to print ∀ or FORALL in some formula depending on whether the style if Plain or
   * Unicode).
   *
   * It is possible that future extensions of OutputModule will support more styles.  Anything
   * printing to an OutputModule should support at least the Plain style, and if the OutputModule
   * uses an unknown style, default to that.
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
   *   %{ruleArrow}, %{typeArrow}, %{lambda}, %{vdash}
   * and most importantly:
   *   codes %s, %t and %r are replaced, in order, by the object of the same index in the given
   *   list:
   *   - for a code %s, the corresponding item must be a String, which is printed as is
   *   - for a code %t, the corresponding item must be a Term
   *   - for a code %r, the corresponding item must be a Rule
   * This is done in such a way that occurrences of the same variable in multiple terms all have
   * the same name, and this name is only used for ONE variable.  (Formally: they are printed
   * using the same naming: TermPrinter.Renaming.)
   * As an aside, %% is replaced by just % (as shorthand for using %s with an argument "%").
   *
   * For example, print("%t %{ruleArrow} %t | %t", [a,b,c]) calls printFinal("a → b | c") if
   * the function queryRuleArrow() returns "→".
   *
   * Additional codes may be supported in specific kinds of OutputModule.
   *
   * Note: it is possible to pass a Pair<Term,Renaming> as one of the Object arguments instead of
   * just a term.  This will lead to the given term being printed with the given Renaming.  Hence,
   * if there is a need to print terms across multiple paragraphs using the same Renaming, then the
   * calling method can use this to do so (but needs to keep track of the Renaming by itself).
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
    for (Rule rule : rules) { println("%r", rule); }
    endTable();
  }

  /**
   * This prints the current status of the OutputModule to StdOut.
   * Note: doing this has the side effect that everything is closed (e.g., paragraphs, tables).
   * The same holds if toString() is called.
   */
  void printToStdout();
}

