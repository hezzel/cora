/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.smt;

import java.util.ArrayList;
import cora.exceptions.IndexingError;

public final class Addition extends IntegerExpression {
  protected ArrayList<IntegerExpression> _children;

  protected void addChild(IntegerExpression child) {
    if (child instanceof Addition) {
      Addition c = (Addition)child;
      for (int i = 1; i <= c.numChildren(); i++) _children.add(c.queryChild(i));
    }
    else _children.add(child);
  }

  /** Constructors are hidden, since IntegerExpressions should be made through the SmtFactory. */
  Addition(IntegerExpression a, IntegerExpression b) {
    _children = new ArrayList<IntegerExpression>();
    addChild(a);
    addChild(b);
  }

  /** Constructors are hidden, since IntegerExpressions should be made through the SmtFactory. */
  Addition(ArrayList<IntegerExpression> args) {
    _children = new ArrayList<IntegerExpression>();
    for (int i = 0; i < args.size(); i++) addChild(args.get(i));
  }

  public int numChildren() {
    return _children.size();
  }

  public IntegerExpression queryChild(int index) {
    if (index <= 0 || index > _children.size()) {
      throw new IndexingError("Addition", "queryChild", index, 1, _children.size());
    }
    return _children.get(index-1);
  }

  public int evaluate() {
    int ret = 0;
    for (int i = 0; i < _children.size(); i++) ret += _children.get(i).evaluate();
    return ret;
  }

  public IntegerExpression multiply(int constant) {
    if (constant == 0) return new IValue(0);
    if (constant == 1) return this;
    ArrayList<IntegerExpression> cs = new ArrayList<IntegerExpression>();
    for (int i = 0; i < _children.size(); i++) cs.add(_children.get(i).multiply(constant));
    return new Addition(cs);
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(+");
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
      case ConstantMultiplication cm -> compareTo(cm.queryChild()) <= 0 ? -1 : 1;
      case Addition a -> {
        for (int i = _children.size(), j = a.numChildren(); i > 0 && j > 0; i--, j--) {
          int c = _children.get(i-1).compareTo(a.queryChild(j));
          if (c != 0) yield c;
        }
        yield _children.size() - a.numChildren();
      }
      case Multiplication m -> -1;
      case Division m -> -1;
      case Modulo m -> -1;
    };
  }
}

