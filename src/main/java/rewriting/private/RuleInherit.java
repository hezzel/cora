/**************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rewriting;

import cora.exceptions.IllegalRuleError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.types.Type;
import cora.terms.Environment;
import cora.terms.Term;
import cora.terms.Variable;

/** This class defines shared functionality for all kinds of rules. */
abstract class RuleInherit implements Rule {
  protected Term _left;
  protected Term _right;

  /** Helper function to return the current classname for use in Errors. */
  private String queryMyClassName() {
    return "RuleInherit (" + this.getClass().getSimpleName() + ")";
  }

  /**
   * Creates a rule with the given left- and right-hand side.
   * If the types don't match, a TypingError is thrown.
   */
  protected RuleInherit(Term left, Term right) {
    if (left == null) throw new NullInitialisationError(queryMyClassName(), "left-hand side");
    if (right == null) throw new NullInitialisationError(queryMyClassName(), "right-hand side");
    // both sides should have the same type
    if (!left.queryType().equals(right.queryType())) {
      throw new TypingError(queryMyClassName(), "constructor", "right-hand side",
                            right.queryType().toString(), left.queryType().toString());
    }
    _left = left;
    _right = right;
    // no variables should occur on the right that don't also occur on the left
    Environment lvars = left.vars();
    Environment rvars = right.vars();
    for (Variable x : rvars) {
      if (!lvars.contains(x)) {
        throw new IllegalRuleError(queryMyClassName(), "right-hand side of rule [" + toString() +
          "] contains variable " + x.toString() + " which does not occur on the left.");
      }   
    }
  }

  public Term queryLeftSide() {
    return _left;
  }

  public Term queryRightSide() {
    return _right;
  }

  public boolean isFirstOrder() {
    return _left.isFirstOrder() && _right.isFirstOrder();
  }

  public Type queryType() {
    return _left.queryType();
  }

  public String toString() {
    StringBuilder builder = new StringBuilder();
    _left.addToString(builder);
    builder.append(" → ");
    _right.addToString(builder);
    return builder.toString();
  }
}

