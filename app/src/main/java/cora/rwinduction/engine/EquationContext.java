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

import java.util.ArrayList;
import java.util.Optional;
import java.util.Set;
import charlie.exceptions.IndexingException;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.printer.PrintableObject;
import charlie.printer.PrinterFactory;
import cora.io.OutputModule;

/**
 * An EquationContext couples an Equation with up to 2 meta-terms that keep track of the equation's
 * history, for the sake of future commands.  Moreover, since users need to be able to refer to
 * specific variables in the interactive prover, we also store a naming for the variables inside the
 * equation, so they are always printed in the same way (and an EquationContext implements the
 * PrintableObject class to control its own printing).  Finally, we keep track of a unique index
 * that will refer to this equation within the proof (and corresponding name)
 *
 * An EquationContext is an immutable structure.
 */
public class EquationContext implements PrintableObject {
  private Equation _equation;
  private Optional<Term> _leftGeq;
  private Optional<Term> _rightGeq;
  private Renaming _varNaming;
  private int _index;

  /**
   * Creates the equation context (leftgr, equation, rightgr), with the given renaming and index
   * (and name E<index>).  Note that the Renaming should contain ALL variables and meta-variables
   * occurring free in the leftgr, rightgr, and the equation, or an Exception will be thrown.  A
   * local copy of the Renaming will be made, so modifying it afterwards is safe.
   */
  public EquationContext(Term leftgr, Equation equation, Term rightgr, int index, Renaming naming) {
    _equation = equation;
    _leftGeq = Optional.of(leftgr);
    _rightGeq = Optional.of(rightgr);
    _index = index;
    _varNaming = naming.copy();
    _varNaming.limitDomain(leftgr, rightgr, _equation.getLhs(), _equation.getRhs(),
                           _equation.getConstraint());
    checkReplaceableNaming();
    checkIndex();
  }

  /**
   * Creates the equation context (•, equation, •), with the given renaming and index (and name
   * E<index>).  Note that the Renaming should contain ALL variables and meta-variables occurring
   * free in the Equation, or an Exception will be thrown.  A local copy of the Renaming will be
   * made, so modifying it afterwards is safe.
   */
  public EquationContext(Equation equation, int index, Renaming naming) {
    _equation = equation;
    _leftGeq = Optional.empty();
    _rightGeq = Optional.empty();
    _index = index;
    _varNaming = naming.copy();
    _varNaming.limitDomain(_equation.getLhs(), _equation.getRhs(), _equation.getConstraint());
    checkReplaceableNaming();
    checkIndex();
  }

  /**
   * Creates the eqatation context (leftgr, equation, rightgr) with the given renaming and index,
   * where leftgr and rightgr may be empty, which represents bullet.
   * The same warnings apply as for the other two (public) constructors.
   */
  public EquationContext(Optional<Term> leftgr, Equation equation, Optional<Term> rightgr,
                         int index, Renaming naming) {
    _equation = equation;
    _leftGeq = leftgr;
    _rightGeq = rightgr;
    _index = index;
    _varNaming = naming.copy();
    _varNaming.limitDomain(leftgr.isEmpty() ? TheoryFactory.trueValue : leftgr.get(),
                           _equation.getLhs(), _equation.getRhs(), _equation.getConstraint(),
                           rightgr.isEmpty() ? TheoryFactory.trueValue : rightgr.get());
    checkReplaceableNaming();
    checkIndex();
  }

  /**
   * Private constructor, only called by our own methods.  This does not copy the Renaming,
   * but does limit its domain and check that it satisfies the requirements.
   */
  private EquationContext(Optional<Term> leftgr, Optional<Term> rightgr, Equation equation,
                          int index, Renaming naming) {
    _equation = equation;
    _leftGeq = leftgr;
    _rightGeq = rightgr;
    _index = index;
    _varNaming = naming;
    // limit the domain
    ArrayList<Term> lst = new ArrayList<Term>(5);
    lst.add(_equation.getLhs());
    lst.add(_equation.getRhs());
    lst.add(_equation.getConstraint());
    leftgr.ifPresent( t -> lst.add(t) );
    rightgr.ifPresent( t -> lst.add(t) );
    _varNaming.limitDomain(lst.toArray(Term[]::new));
    // do checks
    checkReplaceableNaming();
    checkIndex();
  }

  /**
   * Helper function for the constructor.  This ensures that the domain for _varNaming contains all
   * the (meta-)variables occurring in this Equation, and throws an IllegalArgumentException if any
   * are missing.
   */
  private void checkReplaceableNaming() {
    checkReplaceablesIn(_equation.getLhs(), "equation's left-hand side");
    checkReplaceablesIn(_equation.getRhs(), "equation's right-hand side");
    checkReplaceablesIn(_equation.getConstraint(), "constraint of the equation");
    _leftGeq.ifPresent( t -> checkReplaceablesIn(t, "left comparison term of equation context") );
    _rightGeq.ifPresent( t -> checkReplaceablesIn(t, "right comparison term of equation context") );
  }

  /**
   * Helper function for checkReplaceableNaming: checkss that the Replaceables in the given term
   * are all in the naming.
   */
  private void checkReplaceablesIn(Term t, String location) {
    for (Replaceable x : t.freeReplaceables()) {
      if (_varNaming.getName(x) == null) {
        throw new IllegalArgumentException("Unknown replaceable in " + location + ": " + x);
      }
    }
  }

  /**
   * Helper function for the constructor.  This ensures that the index is a positive integer.
   */
  private void checkIndex() {
    if (_index <= 0) throw new IllegalArgumentException("Equation context " + toString() +
      " given index " + _index + "; all indexes must be > 0.");
  }

  /** @return the Equation underlying this EquationContext */
  public Equation getEquation() {
    return _equation;
  }

  /** Returns true if the left-greater term or the right-greater tern is not • */
  public boolean hasExtraTerms() {
    return !_leftGeq.isEmpty() || !_rightGeq.isEmpty();
  }

  /**
   * If the context has the form (•, equation, •), this returns Optional.empty().
   * Otherwise, it necessary has a form (s, equation, t), and this will return s.
   */
  public Optional<Term> getLeftGreaterTerm() {
    return _leftGeq;
  }

  /**
   * If the context has the form (•, equation, •), this returns Optional.empty().
   * Otherwise, it necessary has a form (s, equation, t), and this will return t.
   */
  public Optional<Term> getRightGreaterTerm() {
    return _rightGeq;
  }

  /** Returns the index this equation context has within the proof. */
  public int getIndex() {
    return _index;
  }

  /** Returns the name of this equation context within the proof. */
  public String getName() {
    return "E" + getIndex();
  }

  /**
   * Returns the Renaming to be used for printing the current equation context (or its equation
   * in isolation).  It is allowed to modify this Renaming; doing so will not affect the
   * EquationContext, as a copy is returned.
   */
  public Renaming getRenaming() {
    return _varNaming.copy();
  }

  /**
   * Returns the EquationContext with the same "greater" restrictions on the left and right, and
   * also the same Renaming, but with the given equation and index.
   *
   * Note that the new equation should not introduce new variables (or meta-variables), since that
   * will cause an IllegalArgumentException to be thrown.
   */
  public EquationContext replace(Equation eq, int index) {
    return new EquationContext(_leftGeq, _rightGeq, eq, index, _varNaming.copy());
  }

  /**
   * Returns the EquationContext with the same "greater" restrictions on the left and right, but
   * with the given new Renaming, equation and index.
   */
  public EquationContext replace(Equation eq, Renaming naming, int index) {
    return new EquationContext(_leftGeq, _rightGeq, eq, index, naming.copy());
  }

  /** Prints the equation context to the given printer. */
  @Override
  public void print(Printer p) {
    p.add(getName(),
          ": (",
          _leftGeq.isEmpty() ? p.symbBullet() : p.makePrintable(_leftGeq.get(), _varNaming),
          " , ",
          _equation.makePrintableWith(_varNaming),
          " , ",
          _rightGeq.isEmpty() ? p.symbBullet() : p.makePrintable(_rightGeq.get(), _varNaming),
          ")");
  }

  /**
   * This prints a description to the given output module, potentially using colours, and obscuring
   * the context by only indicating whether the left- and right-hand side of the equation are equal
   * to the corresponding greater terms.
   */
  public void prettyPrint(OutputModule module, boolean useColour) {
    String yellow = useColour ? "\033[1;33m" : "";
    String red = useColour ? "\033[1;31m" : "";
    String reset = useColour ? "\033[0m" : "";
    String l = "", r = "";
    if (_leftGeq.isPresent() && _leftGeq.get().equals(_equation.getLhs())) l = red+" ⦾"+reset;
    if (_rightGeq.isPresent() && _rightGeq.get().equals(_equation.getRhs())) r = red+" ⦾"+reset;
    module.print("%a%a %a%{approx}%a %a%a",
      Printer.makePrintable(_equation.getLhs(), _varNaming), l, yellow, reset,
      Printer.makePrintable(_equation.getRhs(), _varNaming), r);
    if (_equation.isConstrained()) {
      module.print(" %a|%a %a", yellow, reset,
                   Printer.makePrintable(_equation.getConstraint(), _varNaming));
    }
  }

  /**
   * Only for debugging or testing purposes!
   * Use a Printer or OutputModule to properly print an Equation.
   */
  @Override
  public String toString() {
    Printer printer = PrinterFactory.createPrinterNotForUserOutput();
    printer.add(this);
    return printer.toString();
  }
}

