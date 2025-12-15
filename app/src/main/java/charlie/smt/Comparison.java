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

import charlie.util.Pair;

import java.util.ArrayList;

/** Not a public class on purpose: use Constraint, or use Geq0, Is0 or Neq0 directly. */
abstract sealed class Comparison extends Constraint permits Geq0, Is0, Neq0 {
  protected IntegerExpression _expr;

  protected abstract boolean evaluate(int num);
  protected abstract String symbol();
  public abstract Constraint negate();

  protected Comparison(IntegerExpression expr) {
    _expr = expr;
    _simplified = checkSimplified();
  }

  /** Constructor used when comparing two numbers to each other, instead of one to 0. */
  protected Comparison(IntegerExpression left, IntegerExpression right) {
    _expr = new Addition(left, right.multiply(-1));
  }

  public IntegerExpression queryExpression() {
    return _expr;
  }

  public boolean evaluate(Valuation val) {
    return evaluate(_expr.evaluate(val));
  }

  /**
   * Default implementation: checks whether the relation is in simplified form if we are Is0 or
   * Neq0.  The case for Geq0 is implemented within Geq0 itself!
   */
  protected boolean checkSimplified() {
    if (!_expr.isSimplified()) return false;
    return switch (_expr) {
      case IValue i -> false;
      case CMult c -> false;
      case Multiplication m -> false;
      case Addition a -> {
        if (a.queryChild(a.numChildren()) instanceof CMult c) {
          yield c.queryConstant() > 0 &&
                (a.numChildren() > 2 || !(a.queryChild(1) instanceof IValue));
        }
        else yield true;
      }
      default -> true;
    };
  }

  /**
   * Default implementation: simplifies the current constraint if we are Is0 or Neq0.
   * The case for Geq0 is implemented within Geq0 itself!
   */
  public Constraint simplify() {
    if (_simplified) return this;
    IntegerExpression e = _expr;
    if (e instanceof CMult c && c.queryConstant() != 0) e = c.queryChild();
    if (e instanceof Multiplication m) return simplifyMultiplication(m);
    e = e.simplify();
    if (e instanceof CMult c) e = c.queryChild();
    if (e instanceof Multiplication m) return simplifyMultiplication(m);
    if (e instanceof IValue v) return (evaluate(v.queryValue())) ? new Truth() : new Falsehood();
    if (e instanceof Addition a && a.queryChild(a.numChildren()) instanceof CMult c &&
        c.queryConstant() < 0) e = e.negate();
    if (e instanceof Addition a && a.queryChild(a.numChildren()) instanceof CMult c &&
        a.numChildren() == 2 && a.queryChild(1) instanceof IValue i) {
      int k = i.queryValue();
      if (k % c.queryConstant() == 0) e = c.queryChild().add(k / c.queryConstant());
      else if (this instanceof Is0) return new Falsehood();
      else return new Truth();
    }
    if (this instanceof Is0) return new Is0(e);
    else return new Neq0(e);
  }

  /**
   * Helper function for simplify: this returns the simplification for a1 * ... * an R 0,
   * where R is either = or #.
   */
  private Constraint simplifyMultiplication(Multiplication m) {
    ArrayList<Constraint> parts = new ArrayList<Constraint>();
    if (this instanceof Is0) {
      for (int i = 1; i <= m.numChildren(); i++) parts.add(new Is0(m.queryChild(i)));
      return (new Disjunction(parts)).simplify();
    }
    else {
      for (int i = 1; i <= m.numChildren(); i++) parts.add(new Neq0(m.queryChild(i)));
      return (new Conjunction(parts)).simplify();
    }
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(");
    builder.append(symbol());
    builder.append(" ");
    _expr.addToSmtString(builder);
    builder.append(" 0)");
  }

  /**
   * The comparison function returns {-1..1} for a comparison with the same expression, and
   * a value ≤ -2 or ≥ 2 for a comparison with a different expression.
   */
  public int compareTo(Constraint other) {
    return switch (other) {
      case Falsehood f -> 1;
      case Truth t -> 1;
      case BVar x -> 1;
      case NBVar x -> 1;
      case Comparison comp -> {
        int cmp = _expr.compareTo(comp._expr);
        if (cmp != 0) yield cmp * 2;
        yield switch (this) {
          case Is0 i -> (other instanceof Is0) ? 0 : -1;
          case Neq0 n -> (other instanceof Neq0) ? 0 : 1;
          case Geq0 g -> (other instanceof Is0) ? 1 : (other instanceof Geq0) ? 0 : -1;
        };
      }
      case Junction j -> -1;
      case Iff i -> -1;
      case EqS e -> -1;
      case UneqS u -> -1;
    };
  }
}

