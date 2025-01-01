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
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Renaming;
import charlie.terms.TermPrinter;
import charlie.terms.TheoryFactory;
import java.util.Set;

/**
 * The basic data structure representing equations: this is a tuple of a left-hand side, a
 * right-hand side, and a constraint.  Equations are immutable.
 */
public final class Equation {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;

  /** Creates the equation lhs ≈ rhs | constraint */
  public Equation(Term lhs, Term rhs, Term constraint) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = constraint;
  }

  /** Creates the equation lhs ≈ rhs | true */
  public Equation(Term lhs, Term rhs) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = TheoryFactory.createValue(true);
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

  public boolean isConstrained() {
    if (_constraint.toValue() == null) return true;
    return !_constraint.toValue().getBool();
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
   */
  public Equation replaceSubterm(EquationPosition pos, Term replacement) {
    return switch (pos.querySide()) {
      case EquationPosition.Side.Left -> {
        Term l = _lhs.replaceSubterm(pos.queryPosition(), replacement);
        yield new Equation(l, _rhs, _constraint);
      }
      case EquationPosition.Side.Right -> {
        Term r = _rhs.replaceSubterm(pos.queryPosition(), replacement);
        yield new Equation(_lhs, r, _constraint);
      }
    };
  }

  /** Returns an object that can be conveniently printed to an OutputModule. */
  public Pair<String,Object[]> getPrintableObject(Renaming renaming) {
    Pair<Term,Renaming> l = new Pair<Term,Renaming>(_lhs, renaming);
    Pair<Term,Renaming> r = new Pair<Term,Renaming>(_rhs, renaming);
    if (isConstrained()) {
      Pair<Term,Renaming> c = new Pair<Term,Renaming>(_constraint, renaming);
      return new Pair<String,Object[]>("%a %{approx} %a | %a", new Object[] { l, r, c});
    }
    else return new Pair<String,Object[]>("%a %{approx} %a", new Object[] { l, r });
  }

  /*
   * Only for debugging or testing purposes!
   * Use cora.rwinduction.tui.Outputter to properly print an Equation.  (And note that they should
   * typically be printed with the same Renaming, as given by the EquationContext in which the
   * Equation lives.)
   */
  public String toString() {
    TermPrinter printer = new TermPrinter(Set.of());
    return toString(printer.generateUniqueNaming(_lhs, _rhs, _constraint));
  }

  /**
   * Slightly cleverer version of toString that takes an existing renaming into account, but for
   * printing to the user you really should still be using the Outputter and getPrintableObject
   * instead!
   */
  public String toString(Renaming renaming) {
    StringBuilder builder = new StringBuilder();
    TermPrinter printer = new TermPrinter(Set.of());
    printer.print(_lhs, renaming, builder);
    builder.append(" ≈ ");
    printer.print(_rhs, renaming, builder);
    builder.append(" | ");
    printer.print(_constraint, renaming, builder);
    return builder.toString();
  }
}
