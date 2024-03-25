/**************************************************************************************************
 Copyright 2024 Cynthia Kop

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
import java.util.TreeSet;
import cora.exceptions.NullInitialisationError;

/**
 * The SmtFactory is used to create Constraints and IntegerExpressions.
 * Note that all variables have to be made in reference to a specific SmtProblem, since this is
 * how SmtProblems track their variables.
 */
public class SmtFactory {
  /** Creates an integer variable with an index that has not yet been used. */
  public static IVar createIntegerVariable(SmtProblem problem) {
    return problem.createIntegerVariable();
  }

  public static IntegerExpression createValue(int v) {
    return new IValue(v);
  }
  
  public static IntegerExpression createAddition(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("Addition", "left argument");
    if (arg2 == null) throw new NullInitialisationError("Addition", "right argument");
    return new Addition(arg1, arg2);
  }

  public static IntegerExpression createMultiplication(int num, IntegerExpression arg) {
    if (arg == null) throw new NullInitialisationError("Multiplication", "non-constant argument");
    return new Multiplication(new IValue(num), arg);
  }

  public static IntegerExpression createMultiplication(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("Multiplication", "left argument");
    if (arg2 == null) throw new NullInitialisationError("Multiplication", "right argument");
    return new Multiplication(arg1, arg2);
  }

  public static IntegerExpression createNegation(IntegerExpression arg) {
    if (arg == null) throw new NullInitialisationError("Negation", "argument");
    return new ConstantMultiplication(-1, arg);
  }

  public static IntegerExpression createDivision(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("Division", "left argument");
    if (arg2 == null) throw new NullInitialisationError("Division", "right argument");
    return new Division(arg1, arg2);
  }

  public static IntegerExpression createModulo(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("Modulo", "left argument");
    if (arg2 == null) throw new NullInitialisationError("Modulo", "right argument");
    return new Modulo(arg1, arg2);
  }

  /** Creates a boolean variable with an index that has not yet been used. */
  public static BVar createBooleanVariable(SmtProblem problem) {
    return problem.createBooleanVariable();
  }

  public static Constraint createValue(boolean b) {
    if (b) return new Truth();
    else return new Falsehood();
  }

  public static Constraint createTrue() {
    return new Truth();
  }

  public static Constraint createFalse() {
    return new Falsehood();
  }

  public static Constraint createGreater(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("Greater", "left argument");
    if (right == null) throw new NullInitialisationError("Greater", "right argument");
    return new Greater(left, right);
  }

  public static Constraint createSmaller(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("Greater", "reversed right argument");
    if (right == null) throw new NullInitialisationError("Greater", "reversed left argument");
    return new Greater(right, left);
  }

  public static Constraint createGeq(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("Geq", "left argument");
    if (right == null) throw new NullInitialisationError("Geq", "right argument");
    return new Geq(left, right);
  }

  public static Constraint createLeq(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("Geq", "reversed right argument");
    if (right == null) throw new NullInitialisationError("Geq", "reversed left argument");
    return new Geq(right, left);
  }

  public static Constraint createEqual(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("Equal", "left argument");
    if (right == null) throw new NullInitialisationError("Equal", "right argument");
    return new Equal(left, right);
  }

  public static Constraint createUnequal(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("Distinct", "left argument");
    if (right == null) throw new NullInitialisationError("Distinct", "right argument");
    return new Distinct(left, right);
  }

  public static Constraint createNegation(Constraint c) {
    if (c == null) throw new NullInitialisationError("Not", "argument");
    return new Not(c);
  }

  public static Constraint createConjunction(Constraint a, Constraint b) {
    if (a == null) throw new NullInitialisationError("Conjunction", "left argument");
    if (b == null) throw new NullInitialisationError("Conjunction", "right argument");
    return new Conjunction(a, b);
  }

  public static Constraint createDisjunction(Constraint a, Constraint b) {
    if (a == null) throw new NullInitialisationError("Disjunction", "left argument");
    if (b == null) throw new NullInitialisationError("Disjunction", "right argument");
    return new Disjunction(a, b);
  }

  public static Constraint createDisjunction(ArrayList<Constraint> args) {
    if (args == null) throw new NullInitialisationError("Disjunction", "argument list");
    for (int i = 0; i < args.size(); i++) {
      if (args.get(i) == null) {
        throw new NullInitialisationError("Disjunction", "argument " + (i+1));
      }
    }
    if (args.size() == 0) return new Falsehood();
    if (args.size() == 1) return args.get(0);
    return new Disjunction(args);
  }

  public static Constraint createImplication(Constraint a, Constraint b) {
    if (a == null) throw new NullInitialisationError("Implication", "left argument");
    if (b == null) throw new NullInitialisationError("Implication", "right argument");
    return new Disjunction(new Not(a), b);
  }

  public static Constraint createIff(Constraint a, Constraint b) {
    if (a == null) throw new NullInitialisationError("Iff", "left argument");
    if (b == null) throw new NullInitialisationError("Iff", "right argument");
    return new Iff(a, b);
  }
}

