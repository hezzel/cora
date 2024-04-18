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

/** Boolean constraints, to be sent to an SMT solver. */
public sealed abstract class Constraint
  permits BVar, NBVar, Truth, Falsehood, Comparison, Junction, Not, Iff {
  /**
   * This function evaluates the current constraint to its boolean value.  Any variables are
   * interpreted following the given valuation.
   */
  public abstract boolean evaluate(Valuation val);

  /** Adds the SMT description of the current constraint to the given string builder. */
  public abstract void addToSmtString(StringBuilder builder);

  /** Equality check between Constraints */
  public abstract boolean equals(Constraint other);

  /** Returns the negation of the current constraint */
  public abstract Constraint negate();

  /**
   * Assuming the current constraint has no variables, this function evaluates it to its boolean
   * value.  If there is a variable in it, an SmtEvaluationError will be thrown instead.
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

  public boolean equals(Object other) {
    return (other instanceof Constraint) && equals((Constraint)other);
  }

}

