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

package charlie.smt;

import java.util.Arrays;
import java.util.List;
import charlie.exceptions.NullStorageException;

/**
 * The SmtFactory is used to create Constraints and IntegerExpressions.
 * Note that all variables have to be made in reference to a specific SmtProblem, since this is
 * how SmtProblems track their variables.
 */
public class SmtFactory {
  /**
   * Creates an integer variable with an index that has not yet been used, and which has the given
   * bounds.  Throws an IllegalArgumentException if the variable has an empty range.
   *
   * Note: the bounds are only used as a shorthand for requiring that lower ≤ var ≤ higher, and
   * hence are only to be used for SATISFIABILITY problems (as it is certainly not valid that
   * lower ≤ var ≤ higher for all possible assignments to var).  Moreover, they will be removed if
   * you call problem.clear().  
   */
  public static IVar createIntegerVariable(SmtProblem problem, String name, int lower, int higher) {
    IVar ret = problem.createIntegerVariable(name);
    problem.require(new Geq0(ret, new IValue(lower)));
    problem.require(new Geq0(new IValue(higher), ret));
    if (higher < lower) {
      throw new IllegalArgumentException("Cannot create an integer variable in range {" +
        lower + ".." + higher + "}!");
    }
    return ret;
  }

  public static IntegerExpression createValue(int v) {
    return new IValue(v);
  }
  
  public static IntegerExpression createAddition(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullStorageException("Addition", "left argument");
    if (arg2 == null) throw new NullStorageException("Addition", "right argument");
    return new Addition(arg1, arg2);
  }

  public static IntegerExpression createMultiplication(int num, IntegerExpression arg) {
    if (arg == null) throw new NullStorageException("Multiplication", "non-constant argument");
    return new Multiplication(new IValue(num), arg);
  }

  public static IntegerExpression createMultiplication(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullStorageException("Multiplication", "left argument");
    if (arg2 == null) throw new NullStorageException("Multiplication", "right argument");
    return new Multiplication(arg1, arg2);
  }

  public static IntegerExpression createNegation(IntegerExpression arg) {
    if (arg == null) throw new NullStorageException("Negation", "argument");
    return new CMult(-1, arg);
  }

  public static IntegerExpression createDivision(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullStorageException("Division", "left argument");
    if (arg2 == null) throw new NullStorageException("Division", "right argument");
    return new Division(arg1, arg2);
  }

  public static IntegerExpression createModulo(IntegerExpression arg1, IntegerExpression arg2) {
    if (arg1 == null) throw new NullStorageException("Modulo", "left argument");
    if (arg2 == null) throw new NullStorageException("Modulo", "right argument");
    return new Modulo(arg1, arg2);
  }

  /** Creates a string variable with an index that has not yet been used. */
  public static SVar createStringVariable(SmtProblem problem) {
    return problem.createStringVariable();
  }

  public static StringExpression createValue(String s) {
    return new SValue(s);
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
    if (left == null) throw new NullStorageException("Greater", "left argument");
    if (right == null) throw new NullStorageException("Greater", "right argument");
    return new Geq0(left, new Addition(new IValue(1), right));
  }

  public static Constraint createSmaller(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullStorageException("Greater", "reversed right argument");
    if (right == null) throw new NullStorageException("Greater", "reversed left argument");
    return new Geq0(right, new Addition(new IValue(1), left));
  }

  public static Constraint createGeq(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullStorageException("Geq", "left argument");
    if (right == null) throw new NullStorageException("Geq", "right argument");
    return new Geq0(left, right);
  }

  /** Creates left ≥ 0 */
  public static Constraint createGeq(IntegerExpression left) {
    if (left == null) throw new NullStorageException("Geq", "left argument");
    return new Geq0(left);
  }

  public static Constraint createLeq(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullStorageException("Geq", "reversed right argument");
    if (right == null) throw new NullStorageException("Geq", "reversed left argument");
    return new Geq0(right, left);
  }

  public static Constraint createEqual(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullStorageException("Equal", "left argument");
    if (right == null) throw new NullStorageException("Equal", "right argument");
    return new Is0(left, right);
  }

  public static Constraint createEqual(StringExpression left, StringExpression right) {
    if (left == null) throw new NullStorageException("Equal", "left argument");
    if (right == null) throw new NullStorageException("Equal", "right argument");
    return new EqS(left, right);
  }

  /** Creates left = 0 */
  public static Constraint createEqual(IntegerExpression left) {
    if (left == null) throw new NullStorageException("Equal", "left argument");
    return new Is0(left);
  }

  public static Constraint createUnequal(IntegerExpression left, IntegerExpression right) {
    if (left == null) throw new NullStorageException("Distinct", "left argument");
    if (right == null) throw new NullStorageException("Distinct", "right argument");
    return new Neq0(left, right);
  }

  public static Constraint createUnequal(StringExpression left, StringExpression right) {
    if (left == null) throw new NullStorageException("Distinct", "left argument");
    if (right == null) throw new NullStorageException("Distinct", "right argument");
    return new UneqS(left, right);
  }

  /** Creates left != 0 */
  public static Constraint createUnequal(IntegerExpression left) {
    if (left == null) throw new NullStorageException("Equal", "left argument");
    return new Neq0(left);
  }

  public static Constraint createNegation(Constraint c) {
    return c.negate();
  }

  public static Constraint createConjunction(Constraint a, Constraint b) {
    if (a == null) throw new NullStorageException("Conjunction", "left argument");
    if (b == null) throw new NullStorageException("Conjunction", "right argument");
    return new Conjunction(a, b);
  }

  public static Constraint createConjunction(List<Constraint> args) {
    if (args == null) throw new NullStorageException("Conjunction", "argument list");
    for (int i = 0; i < args.size(); i++) {
      if (args.get(i) == null) {
        throw new NullStorageException("Conjunction", "argument " + (i+1));
      }
    }
    if (args.size() == 0) return new Truth();
    if (args.size() == 1) return args.get(0);
    return new Conjunction(args);
  }

  public static Constraint createDisjunction(Constraint a, Constraint b) {
    if (a == null) throw new NullStorageException("Disjunction", "left argument");
    if (b == null) throw new NullStorageException("Disjunction", "right argument");
    return new Disjunction(a, b);
  }

  public static Constraint createDisjunction(List<Constraint> args) {
    if (args == null) throw new NullStorageException("Disjunction", "argument list");
    for (int i = 0; i < args.size(); i++) {
      if (args.get(i) == null) {
        throw new NullStorageException("Disjunction", "argument " + (i+1));
      }
    }
    if (args.size() == 0) return new Falsehood();
    if (args.size() == 1) return args.get(0);
    return new Disjunction(args);
  }

  public static Constraint createDisjunction(Constraint ... reqs) {
    return createDisjunction(Arrays.asList(reqs));
  }

  public static Constraint createImplication(Constraint a, Constraint b) {
    if (a == null) throw new NullStorageException("Implication", "left argument");
    if (b == null) throw new NullStorageException("Implication", "right argument");
    return new Disjunction(a.negate(), b);
  }

  public static Constraint createIff(Constraint a, Constraint b) {
    if (a == null) throw new NullStorageException("Iff", "left argument");
    if (b == null) throw new NullStorageException("Iff", "right argument");
    return new Iff(a, b);
  }
}

