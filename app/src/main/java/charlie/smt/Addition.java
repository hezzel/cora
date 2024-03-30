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

import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.ArrayList;
import charlie.exceptions.IndexingError;

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
    checkSimplified();
  }

  /** Constructors are hidden, since IntegerExpressions should be made through the SmtFactory. */
  Addition(List<IntegerExpression> args) {
    _children = new ArrayList<IntegerExpression>();
    for (IntegerExpression arg : args) addChild(arg);
    checkSimplified();
  }

  /** Private constructor for simplify() when the array does not need to be copied and checked. */
  private Addition(ArrayList<IntegerExpression> args) {
    _children = args;
    _simplified = true;
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

  /** Helper for the constructor: sets the _simplified variable if we are in simplified form. */
  private void checkSimplified() {
    for (int i = 0; i < _children.size(); i++) {
      IntegerExpression child = _children.get(i);
      if (!child.isSimplified()) return;
      if (i == 0) continue;
      IntegerExpression childmain = switch(child) {
        case IValue k -> new IValue(1);
        case CMult m -> m.queryChild();
        default -> child;
      };
      IntegerExpression prevmain = switch(_children.get(i-1)) {
        case IValue k -> new IValue(1);
        case CMult m -> m.queryChild();
        default -> _children.get(i-1);
      };
      if (prevmain.compareTo(childmain) >= 0) return;
    }
    _simplified = true;
  }

  /** Returns a simplified representation of the addition */
  public IntegerExpression simplify() {
    if (_simplified) return this;
    // acquire all children in simplified form
    ArrayList<IntegerExpression> todo = new ArrayList<IntegerExpression>();
    for (IntegerExpression c : _children) {
      c = c.simplify();
      if (c instanceof Addition a) todo.addAll(a._children);
      else todo.add(c);
    }
    // store the children into a treemap so we can count duplicates, but merge the contants directly
    TreeMap<IntegerExpression,Integer> counts = new TreeMap<IntegerExpression,Integer>();
    int constant = 0;
    for (IntegerExpression c : todo) {
      IntegerExpression main;
      int num;
      if (c instanceof IValue k) { constant += k.queryValue(); continue; }
      else if (c instanceof CMult cm) { main = cm.queryChild(); num = cm.queryConstant(); }
      else { main = c; num = 1; }
      Integer current = counts.get(main);
      if (current == null) counts.put(main, num);
      else counts.put(main, num + current);
    }
    // read them out
    ArrayList<IntegerExpression> ret = new ArrayList<IntegerExpression>();
    if (constant != 0) ret.add(new IValue(constant));
    for (Map.Entry<IntegerExpression,Integer> entry : counts.entrySet()) {
      int k = entry.getValue();
      if (k == 1) ret.add(entry.getKey());
      else if (k != 0) ret.add(new CMult(k, entry.getKey()));
    }
    // return the result
    if (ret.size() == 0) return new IValue(0);
    if (ret.size() == 1) return ret.get(0);
    return new Addition(ret);
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
      case CMult cm -> compareTo(cm.queryChild()) <= 0 ? -1 : 1;
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

