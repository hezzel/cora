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

import cora.exceptions.NullInitialisationError;

/** This factory will create integer expressions and constraints. */

public class SmtFactory {
  public static IntegerExpression createValue(int v) {
    return new IValue(v);
  }
  
  public static IntegerExpression createIntegerVariable(int index) {
    return new IVar(index);
  }

  public static IntegerExpression createAddition(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("IPlus", "left argument");
    if (arg2 == null) throw new NullInitialisationError("IPlus", "right argument");
    return new Addition(arg1, arg2);
  }

  public static IntegerExpression createMultiplication(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullInitialisationError("ITimes", "left argument");
    if (arg2 == null) throw new NullInitialisationError("ITimes", "right argument");
    return new Multiplication(arg1, arg2);
  }

  public static IntegerExpression createNegation(IntegerExpression arg) {
    if (arg == null) throw new NullInitialisationError("IMinus", "argument");
    return new Minus(arg);
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

  public static Constraint createBooleanVariable(int index) {
    return new BVar(index);
  }

  public static Constraint createGreater(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BGreater", "left argument");
    if (right == null) throw new NullInitialisationError("BGreater", "right argument");
    return new Greater(left, right);
  }

  public static Constraint createSmaller(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BGreater", "reversed right argument");
    if (right == null) throw new NullInitialisationError("BGreater", "reversed left argument");
    return new Greater(right, left);
  }

  public static Constraint createGeq(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BGeq", "left argument");
    if (right == null) throw new NullInitialisationError("BGeq", "right argument");
    return new Geq(left, right);
  }

  public static Constraint createLeq(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullInitialisationError("BGeq", "reversed right argument");
    if (right == null) throw new NullInitialisationError("BGeq", "reversed left argument");
    return new Geq(right, left);
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
}

