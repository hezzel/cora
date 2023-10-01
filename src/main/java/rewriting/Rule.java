/**************************************************************************************************
 Copyright 2019, 2022, 2023 Cynthia Kop

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

import java.util.ArrayList;
import java.util.Map;
import cora.types.Type;
import cora.terms.*;

/**
 * Rules are the core objects that define the reduction relation in a term rewriting system.  These
 * can be first-order or higher-order, constrained or unconstrained.  They always have the form
 * l → r : φ, although this is viewed as just l → r if there is no constraint.
 */
public class Rule {
  private Term _left;
  private Term _right;
  private Term _constraint;

  /**
   * Creates a rule with the given left- and right-hand side and constraint.
   * No error handling is done for the same reason that the constructor is not public: all Rules
   * should be created through the factory, which is where the correctness checks take place.
   */
  Rule(Term left, Term right, Term constraint) {
    _left = left;
    _right = right;
    _constraint = constraint;
  }

  /** Creates an unconstrained rule with the given left- and right-hand side. */
  Rule(Term left, Term right) {
    _left = left;
    _right = right;
    _constraint = TheoryFactory.createValue(true);
  }

  public Term queryLeftSide() {
    return _left;
  }

  public Term queryRightSide() {
    return _right;
  }

  public Term queryConstraint() {
    return _constraint;
  }

  public Type queryType() {
    return _left.queryType();
  }

  public boolean isFirstOrder() {
    return _left.isFirstOrder() && _right.isFirstOrder() && _constraint.isFirstOrder();
  }

  public boolean isApplicative() {
    return _left.isApplicative() && _right.isApplicative() && _constraint.isApplicative();
  }

  public boolean isPatternRule() {
    return _left.isPattern() && _left.isFunctionalTerm();
  }

  /**
   * This returns whether the rule is a constrained rule -- which is the case if the constraint
   * is anything other than the value true.
   */
  public boolean isConstrained() {
    Value value = _constraint.toValue();
    if (value == null) return false;
    return !value.getBool();
  }


  /**
   * If left * X1 *** Xk has the same type as t, then this function returns k; if no such k exists
   * -1 is returned instead . */
  private int findHeadAdditions(Term t) {
    Type mytype = queryType();
    Type histype = t.queryType();
    int k = 0;
    for (; mytype.isArrowType() && !mytype.equals(histype); k++) {
      mytype = mytype.queryArrowOutputType();
    }
    if (mytype.equals(histype)) return k;
    return -1;
  }

  /**
   * This returns whether the current rule can be applied to t at the head.
   * TODO: constraints are ignored for now.
   */
  public boolean applicable(Term t) {
    int n = t.numberArguments();
    int k = findHeadAdditions(t);
    if (k == -1 || n < k) return false;
    Term head = t.queryImmediateHeadSubterm(n-k);
    return _left.match(head) != null;
  }

  /**
   * If the current rule can be applied to t at the head, this returns the result of a head-most
   * reduction; otherwise it returns null.
   * TODO: constraints are ignored for now.
   */
  public Term apply(Term t) {
    int n = t.numberArguments();
    int k = findHeadAdditions(t);
    if (k == -1) return null;
    Term head = t.queryImmediateHeadSubterm(n-k);
    Substitution subst = _left.match(head);
    if (subst == null) return null;
    ArrayList<Term> args = new ArrayList<Term>();
    for (int i = n-k+1; i <= n; i++) args.add(t.queryArgument(i));
    Term righthead = _right.substitute(subst);
    return righthead.apply(args);
  }

  /** Gives a string representation of the current rule. */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    Map<Replaceable,String> renaming = _left.getUniqueNaming();
    _left.addToString(builder, renaming);
    builder.append(" → ");
    _right.addToString(builder, renaming);
    if (isConstrained()) {
      builder.append(" : ");
      _constraint.addToString(builder, renaming);
    }
    return builder.toString();
  }
}

