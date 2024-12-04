/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.smt;

import java.lang.Comparable;

/** Boolean constraints, to be sent to an SMT solver. */
public sealed abstract class Constraint implements Comparable<Constraint>
  permits BVar, NBVar, Truth, Falsehood, Comparison, Junction, Iff, EqS, UneqS {

  /**
   * This variable should be set to true in the constructor if the Constraint is simplified.
   * Note that being simplified means that all sub-constraints and expressions must also be
   * simplified.
   */
  protected boolean _simplified;

  /**
   * The _simplified variable is set to false by default, but inheriting classes should all set it
   * to true if the class is in fact simplified.
   */
  protected Constraint() {
    _simplified = false;
  }

  /**
   * This function evaluates the current constraint to its boolean value.  Any variables are
   * interpreted following the given valuation.
   */
  public abstract boolean evaluate(Valuation val);

  /** Adds the SMT description of the current constraint to the given string builder. */
  public abstract void addToSmtString(StringBuilder builder);

  /**
   * This generates a total ordering on integer expressions.  Constants (true and false) are
   * guaranteed to be minimal in the ordering (compared to constraints that are not constants).
   */
  public abstract int compareTo(Constraint other);

  /**
   * Returns the negation of the current constraint.  If the current constraint is simplified,
   * then the negation is also guaranteed to be simplified.
   */
  public abstract Constraint negate();

  /**
   * This moves the Constraint into a simplified form.  For the result we have:
   * - in Conjunction, Disjunction and Iff, all children occur in the order given by compareTo,
   *   and without duplicates
   * - Conjunction and Disjunction have at least two children, and none of the children are
   *   constants (true or false)
   * - if the constraint does not have variables, then it is Truth or Falsehood
   * - any sub-constraint and sub-expression is simplified too
   * Some other things may be done, but the above properties are guaranteed.
   *
   * Note that the existing Constraint is not affected, as this is an immutable structure.
   *
   * Calling this again on an already-simplified Constraint just returns the same object, and
   * takes only constant time. (Constraints keep track of whether they have been simplified.)
   */
  public abstract Constraint simplify();

  /** This returns whether the IntegerExpression is currently in simplified form.  */
  public final boolean isSimplified() {
    return _simplified;
  }

  /**
   * Assuming the current constraint has no variables, this function evaluates it to its boolean
   * value.  If there is a variable in it, an SmtEvaluationException will be thrown instead.
   */
  public final boolean evaluate() {
    return evaluate(null);
  }

  public final String toString() {
    ConstraintPrinter printer = new ConstraintPrinter();
    return printer.print(this);
  }

  /** Returns an smt-lib compliant presentation of the current constraint. */
  public final String toSmtString() {
    StringBuilder builder = new StringBuilder();
    addToSmtString(builder);
    return builder.toString();
  }

  public final boolean equals(Object other) {
    return (other instanceof Constraint) && compareTo((Constraint)other) == 0;
  }
}

