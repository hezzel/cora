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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import charlie.exceptions.IndexingError;

public final class Multiplication extends IntegerExpression {
  protected ArrayList<IntegerExpression> _children;

  protected void addChild(IntegerExpression child) {
    switch (child) {
      case Multiplication c:
        for (int i = 1; i <= c.numChildren(); i++) _children.add(c.queryChild(i));
        break;
      case CMult c:
        _children.add(new IValue(c.queryConstant()));
        _children.add(c.queryChild());
        break;
      default:
        _children.add(child);
    }
  }

  /** Constructors are hidden, since IntegerExpressions should be made through the SmtFactory. */
  Multiplication(IntegerExpression a, IntegerExpression b) {
    _children = new ArrayList<IntegerExpression>();
    addChild(a);
    addChild(b);
    checkSimplified();
  }

  /** Constructors are hidden, since IntegerExpressions should be made through the SmtFactory. */
  Multiplication(List<IntegerExpression> args) {
    _children = new ArrayList<IntegerExpression>();
    for (int i = 0; i < args.size(); i++) addChild(args.get(i));
    checkSimplified();
  }

  public int numChildren() {
    return _children.size();
  }

  public IntegerExpression queryChild(int index) {
    if (index <= 0 || index > _children.size()) {
      throw new IndexingError("Multiplication", "queryChild", index, 1, _children.size());
    }
    return _children.get(index-1);
  }

  public int evaluate(Valuation val) {
    int ret = 1;
    for (int i = 0; i < _children.size() && ret != 0; i++) ret *= _children.get(i).evaluate(val);
    return ret;
  }

  /**
   * Helper function for the constructors: sets _simplified if we are simplified.
   * This is exactly the case if the components are listed from small to large (with possible
   * duplicates) and there are no IValue or Addition children.  (Note that it is not possible
   * to have Multiplication or CMult children, as these are removed in the
   * constructor).
   */
  private void checkSimplified() {
    for (int i = 0; i < _children.size(); i++) {
      IntegerExpression child = _children.get(i);
      if (child instanceof IValue || child instanceof Addition) return;
      if (i > 0 && _children.get(i-1).compareTo(child) > 0) return;
    }
    _simplified = _children.size() >= 2;
  }

  /**
   * This simplifies all the elements of from and adds them to to, but takes out the constants:
   * these are multiplied together and returned.  Multiplications in the simplifications of from
   * are expanded.
   */
  private int addSimplifiedChildren(ArrayList<IntegerExpression> from,
                                    ArrayList<IntegerExpression> to) {
    int constant = 1;
    for (IntegerExpression child : from) {
      IntegerExpression c = child.simplify();
      if (c instanceof IValue k) constant *= k.queryValue();
      else if (c instanceof CMult cm) {
        constant *= cm.queryConstant();
        to.add(cm.queryChild());
      }
      else if (c instanceof Multiplication m) {
        constant *= addSimplifiedChildren(m._children, to);
      }
      else to.add(c);
    }
    return constant;
  }

  public IntegerExpression simplify() {
    if (_simplified) return this;
    ArrayList<IntegerExpression> todo = new ArrayList<IntegerExpression>();
    int constant = addSimplifiedChildren(_children, todo);
    Collections.sort(todo);
    if (todo.size() == 0) return new IValue(constant);
    if (todo.size() == 1) return todo.get(0).multiply(constant);

    for (int i = 0; i < todo.size(); i++) {
      if (todo.get(i) instanceof Addition a) {
        ArrayList<IntegerExpression> parts = new ArrayList<IntegerExpression>();
        for (int j = 1; j <= a.numChildren(); j++) {
          todo.set(i, a.queryChild(j));
          parts.add(new Multiplication(todo));
        }
        return (new Addition(parts)).simplify();
      }
    }

    // no additions => we're good!
    return (new Multiplication(todo)).multiply(constant);
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(*");
    for (int i = 0; i < _children.size(); i++) {
      builder.append(" ");
      _children.get(i).addToSmtString(builder);
    }   
    builder.append(")");
  }

  public int compareTo(IntegerExpression other) {
    return switch (other) {
      case IValue v -> 1;
      case IVar x -> 1;
      case CMult cm -> compareTo(cm.queryChild()) <= 0 ? -1 : 1;
      case Addition a -> 1;
      case Multiplication m -> {
        for (int i = _children.size(), j = m.numChildren(); i > 0 && j > 0; i--, j--) {
          int c = _children.get(i-1).compareTo(m.queryChild(j));
          if (c != 0) yield c;
        }
        yield _children.size() - m.numChildren();
      }
      case Division d -> -1;
      case Modulo m -> -1;
    };
  }
}

