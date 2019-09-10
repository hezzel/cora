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
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Environment;
import cora.interfaces.terms.Variable;
import cora.interfaces.rewriting.Rule;

/**
 * A FirstOrderRule is a rule l -> r where l and r are first-order terms of the same sort, l is not a
 * variable, and vars(r) ⊆ vars(l).
 */
public class FirstOrderRule implements Rule {
  private Term _left;
  private Term _right;

  /**
   * Creates a rule with the given left- and right-hand side.
   * If the types don't match, a TypingError is thrown.
   */
  public FirstOrderRule(Term left, Term right) {
    if (left == null) throw new NullInitialisationError("FirstOrderRule", "left-hand side");
    if (right == null) throw new NullInitialisationError("FirstOrderRule", "right-hand side");
    // both sides should have the same sort
    if (!left.queryType().equals(right.queryType())) {
      throw new TypingError("FirstOrderRule", "constructor", "right-hand side",
                            right.queryType().toString(), left.queryType().toString());
    }
    // both sides need to be first-order
    if (!left.queryFirstOrder() || !right.queryFirstOrder()) {
      throw new IllegalRuleError("FirstOrderRule", "terms in rule [" + left.toString() + " → " +
        right.toString() + "] are not first-order.");
    }
    // the right-hand side is not allowed to create new variables
    Environment lvars = left.vars();
    Environment rvars = right.vars();
    for (Variable x : rvars) {
      if (!lvars.contains(x)) {
        throw new IllegalRuleError("FirstOrderRule", "right-hand side of rule [" + left.toString() +
          " → " + right.toString() + "] contains variable " + x.toString() + " which does not " +
          "occur on the left.");
      }
    }
    // the right-hand side should have the form f(...)
    if (left.queryTermKind() != Term.TermKind.FUNCTIONALTERM) {
        throw new IllegalRuleError("FirstOrderRule", "illegal rule [" + left.toString() + " → " +
          right.toString() + "] with a variable as the left-hand side.");
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

  public boolean applicable(Term t) {
    return _left.match(t) != null;
  }

  public Term apply(Term t) {
    Substitution subst = _left.match(t);
    if (subst == null) return null;
    return _right.substitute(subst);
  }

  public String toString() {
    return _left.toString() + " → " + _right.toString();
  }
}

