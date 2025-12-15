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
    _simplified = checkSimplified();
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

  private boolean checkSimplified() {
    if (!_left.isSimplified() || !_right.isSimplified()) return false;
    int c = _left.compareTo(_right);
    if (c >= 0) return false;
    return switch (_left) {
      case Falsehood f -> false;
      case Truth t -> false;
      case BVar x -> !(_right instanceof NBVar y && x.queryIndex() == y.queryIndex());
      case Comparison o -> c <= -2;
      default -> true;
    };
  }

  public Constraint simplify() {
    if (_simplified) return this;
    Constraint l = _left.simplify();
    Constraint r = _right.simplify();
    int c = l.compareTo(r);
    if (c == 0) return new Truth();
    if (c > 0) { Constraint tmp = l; l = r; r = tmp; c = -c; }

    if (l instanceof Falsehood) return r.negate();
    if (l instanceof Truth) return r;
    // x <--> !x is equivalent to false
    if (l instanceof BVar x) {
      if (r instanceof NBVar y && x.queryIndex() == y.queryIndex()) return new Falsehood();
    }
    else if (l instanceof Is0 a && c == -1) { // two comparisons with c == -1 implies the same expr
      // a = 0 <--> a # 0 is equivalent to false
      if (r instanceof Neq0) return new Falsehood();
      // a = 0 <--> a ≥ 0 is equivalent to a ≤ 0: if a = 0 then both sides are true,
      // if a < 0 then both sides are false, and one is false, one is true
      else if (r instanceof Geq0) return (new Geq0(a.queryExpression().negate())).simplify();
    }
    else if (l instanceof Geq0 a && c == -1) {
      // a ≥ 0 <--> a # 0 is equivalent to a > 0: then both are true, and if a < 0 or a = 0, one
      // is true, the other alse
      if (r instanceof Neq0) return (new Geq0(a.queryExpression().add(-1))).simplify();
    }

    return new Iff(l, r);
  }

  /** Helper function for negate() */
  private int queryConstraintKind(Constraint c) {
    return switch(c) {
      case Truth x -> 1;
      case Falsehood x -> 1;
      case BVar x -> 1;
      case NBVar x -> 1;
      case EqS x -> 2;
      case UneqS x -> 2;
      case Iff x -> 3;
      case Comparison x -> 4;
      default -> 5;
    };
  }

  public Constraint negate() {
    Iff ret;
    if (queryConstraintKind(_right) < queryConstraintKind(_left)) {
      ret = new Iff(_left, _right.negate());
    }
    else ret = new Iff(_left.negate(), _right);
    if (_simplified) return ret.simplify();
    else return ret;
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
      case EqS e -> -1;
      case UneqS u -> -1;
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

