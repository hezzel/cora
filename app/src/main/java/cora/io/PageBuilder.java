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

package cora.io;

import java.util.ArrayList;

/**
 * A PageBuilder is an output destination for structured output: paragraphs and tables.
 * Different instances can build this structure into a formatted page of text in different ways;
 * for example as plain text, html or latex.  Alternatively, the text might be printed to the
 * user directly (in an interactive process) rather than being gradually built.
 */
public interface PageBuilder {
  /** Add a single paragraph to the page.  This is in principle text without newlines. */
  void addParagraph(String txt);

  /** Add a table to the page.  (See class below.) */
  void addTable(Table table);

  /* Every PageBuilder must also implement a toStrign() that represents the current status of the
   * page, in so far as it hasn't already been printed.
   */

  /** This class is needed to add table structures to the page. */
  public class Table {
    private ArrayList<ArrayList<String>> _cells;
    private int _numColumns;
    private boolean _rowStarted;
  
    /**
     * Create an empty table (no rows or columns yet).
     *
     * It is not necessary to set dimensions, because these will be determined automatically when
     * you add cells to a given row, or add rows.
     */
    public Table() {
      _cells = new ArrayList<ArrayList<String>>();
      _numColumns = 0;
      _rowStarted = false;
    }
  
    /**
     * Adds a cell to the current row in the table.  If there are no rows yet, or the last just
     * ended, this starts a new row with one cell in it.
     *
     * Note that the number of cells in a row is not limited in principle, and it is allowed for
     * multiple rows to have a different number of cells; this just means that the cells for the
     * corresponding columns in other rows are considered empty.
     */
    public void addCell(String txt) {
      ArrayList<String> row;
      if (_rowStarted) row = _cells.get(_cells.size()-1);
      else {
        row = new ArrayList<String>();
        _cells.add(row);
        _rowStarted = true;
      }
      row.add(txt);
      if (row.size() > _numColumns) _numColumns++;
    }

    /** This returns whether anything has already been printed to the current row. */
    public boolean rowStarted() {
      return _rowStarted;
    }
  
    /** This ends the current row.  Any cells added afterwards will be stored in a new row. */
    public void endRow() {
      _rowStarted = false;
    }
  
    /**
     * Returns the total number of rows that has been created.  This includes a possible last one
     * if any cells have been added but endRow() has not yet been called.
     */
    public int numRows() {
      return _cells.size();
    }
  
    /**
     * Returns the total number of columns in the table; that is, the largest number of cells that
     * any row in the table has.
     */
    public int numColumns() {
      return _numColumns;
    }

    /**
     * Returns the contents of the table in the given row and column, if any.  If row or column
     * is out of bounds (so either negative, or ≥ numRows()/numColumns() respectively), then an
     * IndexOutOfBoundsException is thrown.
     * The same happens if column is negative, but if column is too large, then "" is returned.
     */
    public String getCellContents(int rownum, int columnnum) {
      ArrayList<String> row = _cells.get(rownum);
      if (columnnum >= _numColumns) throw new IndexOutOfBoundsException("Requested column " +
        columnnum + " when _numColumns = " + _numColumns + ".");
      if (columnnum >= row.size()) return "";
      return row.get(columnnum);
    }
  
    /**
     * Returns the largest length that the cell in the given column has for any row, where column
     * should be in {0..numColumns-1}. (If column ≥ numColumns then 0 will be returned, if it is
     * smaller than 0 then an IndexOutOfBoundsException will be thrown.)
     *
     * If some row does not have this many columns, it does not count towards the maximum column
     * size.
     */
    public int getColumnSize(int column) {
      int ret = 0;
      for (ArrayList<String> row : _cells) {
        if (column < row.size()) {
          int n = row.get(column).length();
          if (n > ret) ret = n;
        }
      }
      return ret;
    }

    /** Returns an ArrayList that returns all the column sizes in one go. */
    public ArrayList<Integer> getColumnSizes() {
      ArrayList<Integer> ret = new ArrayList<Integer>(_numColumns);
      for (int i = 0; i < _numColumns; i++) ret.add(getColumnSize(i));
      return ret;
    }

    /**
     * Returns a string representation of this table, already formatted with the right whitespace
     * for convenient printing to text output (in a monospaced font).
     */
    public String toString() {
      StringBuilder ret = new StringBuilder();
      ArrayList<Integer> width = getColumnSizes();
      for (ArrayList<String> row : _cells) {
        ret.append("  ");  // indent
        int space = 0;
        for (int x = 0; x < _numColumns; x++) {
          String txt = (x >= row.size() ? "" : row.get(x));
          if (txt.equals("")) space += width.get(x) + 1;
          else {
            space += txt.length();
            ret.append(String.format("%" + space + "s", txt));
            space = width.get(x) + 1 - txt.length();
          }
        }
        ret.append("\n");
      }
      return ret.toString();
    }
  }
}

