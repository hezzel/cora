/**************************************************************************************************
 Copyright 2019 Cynthia Kop

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
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Variable;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Environment;
import cora.interfaces.rewriting.Rule;

/** This class defines shared functionality for all kinds of rules. */
abstract class RuleInherit {
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
    // the free variables in the left-hand side may not be binder variables
    Environment lvars = left.vars();
    for (Variable x : lvars) {
      if (x.isBinderVariable()) {
        throw new IllegalRuleError("RuleInherit", "left-hand side of applicative rule [" +
          left.toString() + " → " + right.toString() + "] freely uses a binder variable!");
      }   
    } 
    // the free variables in the right-hand side must all occur on the left
    Environment rvars = right.vars();
    for (Variable x : rvars) {
      if (!lvars.contains(x)) {
        throw new IllegalRuleError("RuleInherit", "right-hand side of rule [" + left.toString() +
          " → " + right.toString() + "] contains variable " + x.toString() + " which does not " +
          "occur on the left.");
      }
    }
    _left = left;
    _right = right;
  }

  public Term queryLeftSide() {
    return _left;
  }

  public Term queryRightSide() {
    return _right;
  }

  public Type queryType() {
    return _left.queryType();
  }

  public String toString() {
    return _left.toString() + " → " + _right.toString();
  }
}

