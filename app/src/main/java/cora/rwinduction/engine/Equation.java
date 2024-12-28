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

package cora.rwinduction.engine;

import charlie.exceptions.IndexingException;
import charlie.terms.*;
import java.util.Set;

/**
 * The basic data structure representing equations: this is a tuple of a left-hand side, a
 * right-hand side, and a constraint.  Moreover, since users need to be able to refer to specific
 * variables in the interactive prover, we also store a naming for the variables inside the
 * equation, so they are always printed in the same way.
 */
public class Equation {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;
  private int _index;
  private Renaming _varNaming;

  /**
   * Creates the given equation.  Note that the Renaming should contain ALL variables and
   * meta-variables occurring free in the left-hand side, right-hand side, and constraints, or an
   * Exception will be thrown.  A local copy of the Renaming will be made, so modifying it
   * afterwards is safe.
   */
  public Equation(Term lhs, Term rhs, Term constraint, int index, Renaming varNaming) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = constraint;
    _index = index;
    _varNaming = varNaming.copy();
    checkReplaceableNaming();
    checkIndex();
  }

  /**
   * Creates the given equation, with constraint true.  Note that the Renaming should contain ALL
   * variables and meta-variables occurring free in the left-hand side, right-hand side, and
   * constraints, or an Exception will be thrown.  A local copy of the Renaming will be made, so
   * modifying it afterwards is safe.
   */
  public Equation(Term lhs, Term rhs, Renaming varNaming, int index) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = TheoryFactory.createValue(true);
    _index = index;
    _varNaming = varNaming.copy();
    checkReplaceableNaming();
    checkIndex();
  }

  /**
   * Helper function for the constructor.  This ensures that the domain for _varNaming consists of
   * exactly the (meta-)variables occurring in this Equation, and throws an IllegalArgumentException
   * if any are missing.
   */
  private void checkReplaceableNaming() {
    _varNaming.limitDomain(_lhs, _rhs, _constraint);
    Set<Replaceable> dom = _varNaming.domain();
    for (Replaceable x : _lhs.freeReplaceables()) {
      if (!dom.contains(x)) {
        throw new IllegalArgumentException("Unknown replaceable in equation left-hand side: " + x);
      }
    }
    for (Replaceable x : _rhs.freeReplaceables()) {
      if (!dom.contains(x)) {
        throw new IllegalArgumentException("Unknown replaceable in equation right-hand side: " + x);
      }
    }
    for (Replaceable x : _constraint.freeReplaceables()) {
      if (!dom.contains(x)) {
        throw new IllegalArgumentException("Unknown replaceable in equation constraint: " + x);
      }
    }
  }

  /**
   * Helper function for the constructor.  This ensures that the index is a positive integer.
   */
  private void checkIndex() {
    if (_index <= 0) throw new IllegalArgumentException("Equation " + toString() + " given " +
      "index " + _index + "; all indexes must be > 0.");
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

  public int getIndex() {
    return _index;
  }

  public String getName() {
    return "E" + getIndex();
  }

  public boolean isConstrained() {
    if (_constraint.toValue() == null) return true;
    return !_constraint.toValue().getBool();
  }

  /**
   * Warning: the caller may check the given Renaming and use it for printing and parsing, but
   * should not modify it, since the internal stored Renaming is returned for this (so changing
   * it will also affect future calls to getRenaming).
   */
  public Renaming getRenaming() {
    return _varNaming;
  }

  /**
   * Returns the subterm at the given position, assuming that this is indeed a position of the
   * current term.  Otherwise, returns null.
   */
  public Term querySubterm(EquationPosition pos) {
    Term t = pos.querySide() == EquationPosition.Side.Left ? _lhs : _rhs;
    try { return t.querySubterm(pos.queryPosition()); }
    catch (IndexingException e) { return null; }
  }

  /**
   * Replaces the subterm at the given position, assuming that this is indeed a position of the
   * current term and the types match.  Otherwise, throws an appropriate RuntimeException.
   *
   * It is required that all Replaceables in the replacement already occur in this equation's
   * renaming (except for variables that are captured by placing the replacement at the given
   * position); if not, an IllegalArgumentException will be thrown.
   *
   * The newly returned Equation will be given newIndex as its index.
   */
  public Equation replaceSubterm(EquationPosition pos, Term replacement, int newIndex) {
    return switch (pos.querySide()) {
      case EquationPosition.Side.Left -> {
        Term l = _lhs.replaceSubterm(pos.queryPosition(), replacement);
        yield new Equation(l, _rhs, _constraint, newIndex, _varNaming);
      }
      case EquationPosition.Side.Right -> {
        Term r = _rhs.replaceSubterm(pos.queryPosition(), replacement);
        yield new Equation(_lhs, r, _constraint, newIndex, _varNaming);
      }
    };
  }

  /**
   * Only for debugging or testing purposes!
   * Use cora.rwinduction.tui.Outputter to properly print an Equation.
   */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    TermPrinter printer = new TermPrinter(Set.of());
    builder.append("" + _index + ": ");
    printer.print(_lhs, _varNaming, builder);
    builder.append(" ≈ ");
    printer.print(_rhs, _varNaming, builder);
    builder.append(" | ");
    printer.print(_constraint, _varNaming, builder);
    return builder.toString();
  }
}
