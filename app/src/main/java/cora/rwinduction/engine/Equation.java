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
   * Helper function for replaceSubterm: this creates a copy of Renaming appropriate for the new
   * equation, 
   */
  private Renaming limitRenaming(Renaming original, Term l, Term r, Term c) {
    Renaming ret = original.copy();
    ret.limitDomain(l, r, c);
    Set<Replaceable> dom = ret.domain();
    for (Replaceable x : l.freeReplaceables()) {
      if (!dom.contains(x)) throw new IllegalArgumentException("Fresh var in replacement: " + x);
    }
    for (Replaceable x : r.freeReplaceables()) {
      if (!dom.contains(x)) throw new IllegalArgumentException("Fresh var in replacement: " + x);
    }
    for (Replaceable x : c.freeReplaceables()) {
      if (!dom.contains(x)) throw new IllegalArgumentException("Fresh var in replacement: " + x);
    }
    if (dom.size() == original.size()) return original;
    return ret;
  }

  /**
   * Replaces the subterm at the given position, assuming that this is indeed a position of the
   * current term and the types match.  Otherwise, throws an appropriate RuntimeException.
   * It is required that all Replaceables in the replacement already occur in this equation's
   * renaming (except for variables that are captured by placing the replacement at the given
   * position); if not, an IllegalArgumentException will be thrown.
   */
  public Equation replaceSubterm(EquationPosition pos, Term replacement) {
    return switch (pos.querySide()) {
      case EquationPosition.Side.Left -> {
        Term l = _lhs.replaceSubterm(pos.queryPosition(), replacement);
        Renaming ren = limitRenaming(_varNaming, l, _rhs, _constraint);
        yield new Equation(l, _rhs, _constraint, ren);
      }
      case EquationPosition.Side.Right -> {
        Term r = _rhs.replaceSubterm(pos.queryPosition(), replacement);
        Renaming ren = limitRenaming(_varNaming, _lhs, r, _constraint);
        yield new Equation(_lhs, r, _constraint, ren);
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
    printer.print(_lhs, _varNaming, builder);
    builder.append(" ≈ ");
    printer.print(_rhs, _varNaming, builder);
    builder.append(" | ");
    printer.print(_constraint, _varNaming, builder);
    return builder.toString();
  }
}
