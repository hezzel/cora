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

package cora.termination.dependency_pairs;

import charlie.types.TypePrinter;
import charlie.terms.position.PositionPrinter;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;
import charlie.printer.PrinterFactory;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Dependency Pair for Logically Constrained Simply-typed Term Rewrite Systems
 * (LCSTRSs) as introduced in:
 *<p>
 * Liye Guo, Kasper Hagens, Cynthia Kop, Deivid Vale:
 * Higher-Order Constrained Dependency Pairs for (Universal) Computability.
 * MFCS 2024: 57:1-57:15
 *
 * @param lhs the left-hand side of the DP
 * @param rhs the right-hand side of the DP
 * @param constraint the constraint of the DP
 * @param lvars those variables of the DP that must be instantiated with
 *             theory terms; must contain all variables of constraint
 */
public record DP(Term lhs, Term rhs, Term constraint, Set<Variable> lvars)
                                                                       implements PrintableObject {
  /** This verifies that all variables in the constraint are in the list */
  private static boolean initialVarSetCondition(Term constraint, Set<Variable> set) {
    return set.containsAll(constraint.vars().toSet());
  }

  /**
   * Default constructor: creates a DP with the given left-hand side, right-hand side, constraint
   * and logical variables; the set of logical variables must contain all the variables occurring
   * in constraint, or an IllegalArgumentException will be thrown.
   */
  public DP(Term lhs, Term rhs, Term constraint, Set<Variable> lvars) {
    this.lhs = lhs;
    this.rhs = rhs;
    this.constraint = constraint;
    // the initial condition must be satisfied, otherwise we don't even create
    // the DP object, the lower bound however is higher than Vars(Phi)
    // and that's why we compute it here at object creation
    if (initialVarSetCondition(constraint, lvars)) this.lvars = lvars;
    else {
      throw new IllegalArgumentException("Illegal DP construction: the list of variables " +
        lvars + " for the DP must contain at least the variables in the constraint " +
        constraint.toString() + ".");
    }
  }

  /**
   * Creates a DP with the given left-hand side, right-hand side and constraint.  The logical
   * variables will automatically be set to the variables occurring in the constraint.
   */
  public DP(Term lhs, Term rhs, Term constraint) {
    this(lhs, rhs, constraint, constraint.vars().toSet());
  }

  /** Creates a new DP of the form s ⇒ t | true {}, to be used for unconstrained rewriting. */
  public DP(Term lhs, Term rhs) {
    this(lhs, rhs, TheoryFactory.createValue(true), Set.of());
  }

  /**
   * @return a modifiable set of all variables occurring in this DP
   */
  public LinkedHashSet<Variable> getAllVariables() {
    LinkedHashSet<Variable> result = new LinkedHashSet<>();
    for (Variable x : this.lhs.vars()) result.add(x);
    for (Variable x : this.rhs.vars()) result.add(x);
    for (Variable x : this.constraint.vars()) result.add(x);
    return result;
  }

  /**
   * @return a DP that is structurally equivalent to the present one but uses fresh variables
   */
  public DP getRenamed() {
    Substitution subst = TermFactory.createEmptySubstitution();
    for (Variable x : getAllVariables()) {
      subst.extend(x, TermFactory.createVar(x.queryName(), x.queryType()));
    }
    Term newLhs = this.lhs.substitute(subst);
    Term newRhs = this.rhs.substitute(subst);
    Term newConstraint = this.constraint.substitute(subst);
    Set<Variable> newTheoryVars = new LinkedHashSet<>();
    for (Variable x : this.lvars) {
      Term y = subst.get(x);
      if (y != null) newTheoryVars.add(y.queryVariable());
    }
    return new DP(newLhs, newRhs, newConstraint, newTheoryVars);
  }

  /** This function properly prints a DP to a Printer (which is also used by OutputModule). */
  @Override
  public void print(Printer printer) {
    Renaming renaming = printer.generateUniqueNaming(this.lhs, this.rhs, this.constraint);
    printWithRenaming(printer, renaming);
  }

  /**
   * This function creates a printable object for printing the DP under a specific Renaming.
   * Note that the Renaming is expected to contain all the variables in left, right and constraint,
   * and only those.  Variables that occur in lvars but not in the terms should not be included, as
   * it would only be confusing to print them.
   */
  public PrintableObject makePrintableWith(Renaming renaming) {
    return new PrintableObject() {
      public void print(Printer printer) {
        printWithRenaming(printer, renaming);
      }
    };
  }

  /** This function prints the DP using the given Renaming. */
  private void printWithRenaming(Printer printer, Renaming naming) {
    // left ⇒ right
    printer.add(printer.makePrintable(this.lhs, naming), " ",
                printer.symbThickArrow(), " ",
                printer.makePrintable(this.rhs, naming));
    // | constraint
    if (!this.constraint.isValue() || this.constraint.toValue().getBool()) {
      printer.add(" | ", printer.makePrintable(this.constraint, naming));
    }
    // { x1, ..., xn }
    boolean anynew = false;
    for (Variable x : this.lvars) {
      if (!this.constraint.freeReplaceables().contains(x)) anynew = true;
    }
    if (!anynew) return;
    boolean first = true;
    for (Variable x : this.lvars) {
      if (naming.getName(x) == null) continue;
      if (constraint.vars().contains(x)) continue;
      if (first) printer.add(" { ");
      else printer.add(", ");
      first = false;
      printer.add(naming.getName(x));
    }
    if (!first) printer.add(" }");
  }

  /**
   * Default toString() functionality; deliberately ugly because printing to the user should always
   * be done through an output module / printer.
   */
  @Override
  public String toString() {
    Printer printer = PrinterFactory.createDebugPrinter();
    Renaming renaming = printer.generateUniqueNaming(lhs, rhs, constraint);
    printWithRenaming(printer, renaming);
    return printer.toString();
  }

  /** Returns a string representation for unit testing (so without nasty variable indexes). */
  public String ustr() {
    Printer printer = PrinterFactory.createPrinterNotForUserOutput();
    Renaming renaming = printer.generateUniqueNaming(lhs, rhs, constraint);
    printWithRenaming(printer, renaming);
    return printer.toString();
  }
}

