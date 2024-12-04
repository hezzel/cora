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

public final class Geq0 extends Comparison {
  Geq0(IntegerExpression expr) { super(expr); }
  Geq0(IntegerExpression left, IntegerExpression right) { super(left, right); }
  protected boolean evaluate(int num) { return num >= 0; }
  protected String symbol() { return ">="; }
  public int hashCode() { return 17 * _expr.hashCode() + 4; }

  public Constraint negate() {
    Constraint ret = new Geq0(_expr.negate().add(-1));
    if (_simplified) return ret.simplify();
    return ret;
  }

  protected boolean checkSimplified() {
    if (!_expr.isSimplified() || _expr instanceof IValue) return false;
    if (_expr instanceof CMult c) { return c.queryConstant() == -1; }
    if (_expr instanceof Addition a &&
        a.queryChild(a.numChildren()) instanceof CMult c &&
        a.numChildren() == 2 && a.queryChild(1) instanceof IValue) {
      return c.queryConstant() == -1;
    }
    return true;
  }

  public Constraint simplify() {
    if (_simplified) return this;
    // we apply removeCMult both before and after simplifying, because the simplify step might
    // destroy an earlier CMult (or create one from a more complex expression)
    IntegerExpression e = removeCMult(removeCMult(_expr).simplify());
    if (e instanceof IValue v) { return v.queryValue() >= 0 ? new Truth() : new Falsehood(); }
    if (e instanceof Addition ad && ad.numChildren() == 2 && ad.queryChild(1) instanceof IValue k &&
        ad.queryChild(2) instanceof CMult c && c.queryConstant() != -1) {
      int a = c.queryConstant();
      int b = k.queryValue();
      if (a > 1) {
        // a x ≥ -b <==> x ≥ CEIL(-b/a)
        int v = b < 0 ? -((-b + a - 1) / a) : b / a;
        if (v == 0) e = c.queryChild();
        else e = new Addition(new IValue(v), c.queryChild());
      }
      else {  // a < -1
        // b ≥ -a x <==> x ≤ FLOOR(b/-a)
        int v = b > 0 ? b / -a : -((-b - a - 1) / -a);
        if (v == 0) e = new CMult(-1, c.queryChild());
        else e = new Addition(new IValue(v), new CMult(-1, c.queryChild()));
      }
    }
    return new Geq0(e);
  }

  /** Helper function for simplify: removes a CMult taking signs into account. */
  protected IntegerExpression removeCMult(IntegerExpression e) {
    if (e instanceof CMult c) {
      int k = c.queryConstant();
      if (k > 0) return c.queryChild();
      if (k < -1) return new CMult(-1, c.queryChild());
    }
    return e;
  }

}

