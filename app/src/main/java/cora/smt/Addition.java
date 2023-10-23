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

class Addition extends IntegerExpression {
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

  public void addToSmtString(StringBuilder builder) {
    builder.append("(+");
    for (int i = 0; i < _children.size(); i++) {
      builder.append(" ");
      _children.get(i).addToSmtString(builder);
    }   
    builder.append(")");
  }

  public boolean equals(IntegerExpression other) {
    if (!(other instanceof Addition)) return false;
    Addition a = (Addition)other;
    if (a.numChildren() != _children.size()) return false;
    for (int i = 0; i < _children.size(); i++) {
      if (!_children.get(i).equals(a.queryChild(i+1))) return false;
    }
    return true;
  }
}

