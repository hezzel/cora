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

public final class Iff extends Constraint {
  private Constraint _left;
  private Constraint _right;

  /** The constructor is hidden, since Constraints should be made through the SmtFactory. */
  Iff(Constraint a, Constraint b) {
    _left = a;
    _right = b;
  }

  public Constraint queryLeft() {
    return _left;
  }

  public Constraint queryRight() {
    return _right;
  }

  public boolean evaluate(Valuation val) {
    return _left.evaluate(val) == _right.evaluate(val);
  }

  /** Helper function for negate() */
  private int queryConstraintKind(Constraint c) {
    return switch(c) {
      case BVar x -> 1;
      case NBVar x -> 1;
      case Iff x -> 2;
      case Comparison x -> 3;
      default -> 4;
    };
  }

  public Iff negate() {
    if (queryConstraintKind(_right) < queryConstraintKind(_left)) {
      return new Iff(_left, _right.negate());
    }
    else return new Iff(_left.negate(), _right);
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(= ");
    _left.addToSmtString(builder);
    builder.append(" ");
    _right.addToSmtString(builder);
    builder.append(")");
  }

  public int compareTo(Constraint other) {
    return switch (other) {
      case EqS _ -> -1;
      case UneqS _ -> -1;
      case Iff iff -> {
        int c = _left.compareTo(iff._left);
        if (c == 0) c = _right.compareTo(iff._right);
        yield c;
      }
      default -> 1;
    };
  }

  public int hashCode() { return 17 * (_left.hashCode() * 31 + _right.hashCode()) + 7; }
}

