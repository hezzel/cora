package cora.parsing;

/** A position in a file or line; for convenient printing in error messages. */
class ParsePosition {
  private String _file;
  private int _line;
  private int _pos;

  /**
   * Sets the parse position to the give file, line and position in the line.
   * Note that filename is allowed to be null (indicating that no file should be printed for this
   * position), and if filename is null, then line is allowed to be 0 (indicating that no line
   * should be printed for this position).
   *
   * Note that line should be ≥ 0, and pos should be > 0 for this to be a meaningful position
   * (though no errors will be thrown if this rule is violated).
   */
  ParsePosition(String filename, int line, int pos) {
    _file = filename;
    _line = line;
    _pos = pos;
  }

  /**
   * Sets the parse position to the give line and position in the line.  As no filename is given,
   * no file will be printed for this position, and getFile() will return null.  If line is set to
   * 0, then no line will be printed either.
   *
   * Note that line should be ≥ 0, and pos should be > 0 for this to be a meaningful position
   * (though no errors will be thrown if this rule is violated).
   */
  ParsePosition(int line, int pos) {
    _file = null;
    _line = line;
    _pos = pos;
  }

  /**
   * Sets the parse position to the given index.  No file or line will be printed for this parse
   * position; getFile() will return null and getLine() will return 0.
   *
   * Note that pos should be > 0 for this to be a meaningful position (though no errors will be
   * thrown if this rule is violated).
   */
  ParsePosition(int pos) {
    _file = null;
    _line = 0;
    _pos = pos;
  }

  /** Returns the file this position is set to, or null if no file was set. */
  String getFile() {
    return _file;
  }

  /** Returns the line this position is set to, or 0 if no line was set. */
  int getLine() {
    return _line;
  }

  /**
   * Returns the x position of the current position; either in a given string,
   * or in a single line.
   */
  int getPosition() {
    return _pos;
  }

  /** Returns a new ParsePosition with the position in line increased by offset. */
  ParsePosition increasePosition(int offset) {
    return new ParsePosition(_file, _line, _pos + offset);
  }

  /** Returns a string representation of the current position. */
  public String toString() {
    String p = "" + _pos;
    if (_pos <= 0) p = "<unknown position>";
    if (_file == null && _line == 0) return "" + p;
    if (_file == null) return _line + ":" + p;
    return _file + ":" + _line + ":" + p;
  }
}
