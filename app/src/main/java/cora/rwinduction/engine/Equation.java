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
import charlie.terms.Renaming;
import charlie.terms.Term;
import charlie.terms.TermPrinter;
import charlie.terms.TheoryFactory;
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
  private Renaming _varNaming;

  public Equation(Term lhs, Term rhs, Term constraint, Renaming varNaming) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = constraint;
    _varNaming = varNaming;
  }

  public Equation(Term lhs, Term rhs, Renaming varNaming) {
    _lhs = lhs;
    _rhs = rhs;
    _constraint = TheoryFactory.createValue(true);
    _varNaming = varNaming;
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
   * Only for debugging or testing purposes!
   * Use cora.rwinduction.tui.Outputter to properly print an Equation.
   */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    TermPrinter printer = new TermPrinter(Set.of());
    printer.print(_lhs, _varNaming, builder);
    builder.append(" ≈ ");
    printer.print(_rhs, _varNaming, builder);
    builder.append(" | ");
    printer.print(_constraint, _varNaming, builder);
    return builder.toString();
  }
}
