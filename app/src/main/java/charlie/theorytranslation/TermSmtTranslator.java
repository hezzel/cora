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

package charlie.theorytranslation;

import java.util.TreeMap;
import charlie.exceptions.TypingException;
import charlie.exceptions.UnsupportedTheoryException;
import charlie.types.TypeFactory;
import charlie.terms.*;
import charlie.smt.*;

/**
 * This class provides translations between theory terms and SMT expressions.
 *
 * To use it:
 * - create an SmtProblem (it doesn't need to be fresh; it's allowed to already contain some
 *   variables and requirements)
 * - create a TermSmtTranslator with the SmtProblem as parameter
 * - use the translator to translate one or more terms to IntegerExpressions / StringExpressions /
 *   Constraints
 * - add what constraints you want to the SmtProblem (these could be the translated constraints,
 *   constraints obtained from restructuring them (e.g., wrapping them in a larger constraint),
 *   or entirely new (so long as the variables for the constraint are all created  for the same
 *   SmtProblem)
 * - use an SmtSolver to query satisfiability or validity of the SmtProblem
 *
 * For convenience, some extra functions have been supplied:
 * - you can generate the translator without an SmtProblem; in this case a new SmtProblem is
 *   created (and can be queried using queryProblem())
 * - you can immediately "require" theory terms of type Bool, rather than first translating this
 *   term and then requiring it in the underlying SmtProblem.
 */
public class TermSmtTranslator {
  private SmtProblem _problem;
  private TreeMap<Variable,IVar> _ivars;
  private TreeMap<Variable,SVar> _svars;
  private TreeMap<Variable,BVar> _bvars;
  private TreeMap<IVar,Variable> _varOfIVar;

  /**
   * Create a translator for transforming terms into SMT expressions.  The given SmtProblem is used
   * to create and store the SMT variables corresponding to the term variables.
   */
  public TermSmtTranslator(SmtProblem problem) {
    _problem = problem;
    _ivars = new TreeMap<Variable,IVar>();
    _svars = new TreeMap<Variable,SVar>();
    _bvars = new TreeMap<Variable,BVar>();
    _varOfIVar = new TreeMap<IVar,Variable>();
  }

  /**
   * Create a translator for transforming terms into SMT expressions.  All variables are created
   * with reference to a fresh SmtProblem.
   */
  public TermSmtTranslator() {
    _problem = new SmtProblem();
    _ivars = new TreeMap<Variable,IVar>();
    _svars = new TreeMap<Variable,SVar>();
    _bvars = new TreeMap<Variable,BVar>();
    _varOfIVar = new TreeMap<IVar,Variable>();
  }

  /** Returns the SmtProblem associated to this translator (and used for translating variables). */
  public SmtProblem queryProblem() {
    return _problem;
  }

  /**
   * Helper function for multiple translate methods; given a term that *should* be a functional
   * term with a calculation as its root, returns that calculation symbol (and throws some errors
   * if the term does not have the expected shape).
   */
  private CalculationSymbol getCalculationRoot(Term t) {
    if (!t.isFunctionalTerm()) {
      throw new UnsupportedTheoryException(t.toString(), "expected variable or functional term");
    }
    FunctionSymbol root = t.queryRoot();
    CalculationSymbol calc = root.toCalculationSymbol();
    if (calc == null) {
      throw new UnsupportedTheoryException(t.toString(),
                                       "root " + root.toString() + " is not a calculation symbol");
    }
    return calc;
  }

  /**
   * If the given variable has been used before, returns the same IVar as we used then; otherwise,
   * generates a new IVar and both stores and returns it.
   */
  private IVar getIntegerVariableFor(Variable x) {
    if (!_ivars.containsKey(x)) {
      IVar ivar = _problem.createIntegerVariable();
      _ivars.put(x, ivar);
      _varOfIVar.put(ivar, x);
    }
    return _ivars.get(x);
  }

  /**
   * If the given variable has been used before, returns the same SVar as we used then; otherwise,
   * generates a new SVar and both stores and returns it.
   */
  private SVar getStringVariableFor(Variable x) {
    if (!_svars.containsKey(x)) _svars.put(x, _problem.createStringVariable());
    return _svars.get(x);
  }

  /**
   * If the given variable has been used before, returns the same BVar as we used then; otherwise,
   * generates a new BVar and both stores and returns it.
   */
  private BVar getBooleanVariableFor(Variable x) {
    if (!_bvars.containsKey(x)) _bvars.put(x, _problem.createBooleanVariable());
    return _bvars.get(x);
  }

  /**
   * This returns the integer variable that corresponds to the given user Variable, if any.  If
   * this has not been used, null is returned instead.
   */
  public IVar getIVar(Variable x) {
    return _ivars.get(x);
  }

  /**
   * This returns the string variable that corresponds to the given user Variable, if any.  If
   * this has not been used, null is returned instead.
   */
  public SVar getSVar(Variable x) {
    return _svars.get(x);
  }

  /**
   * This returns the boolean variable that corresponds to the given user Variable, if any.  If
   * this has not been used, null is returned instead.
   */
  public BVar getBVar(Variable x) {
    return _bvars.get(x);
  }

  /**
   * This is the inverse of getIVar(), i.e., it returns the user Variable that corresponds to the
   * given integer variable.
   */
  public Variable getVarOfIVar(IVar ivar) {
    return _varOfIVar.get(ivar);
  }

  /**
   * Helper interface so the translate function can handle all kinds of symbols and values in one
   * big switch (which is important so we get compiler errors if someone adds a kind of calculation
   * symbol but fails to add a corresponding translation).
   */
  private sealed interface Exp {
    public record I(IntegerExpression iexp) implements Exp {}
    public record S(StringExpression sexp) implements Exp {}
    public record B(Constraint bexp) implements Exp {}
  }

  /**
   * Translates a term to the corresponding Constraint or IntegerExpression.  Basically a unifying
   * function for translateIntegerExpression and translateContraint.
   */
  private Exp translate(Term t) {
    if (t.isVariable()) {
      Variable x = t.queryVariable();
      if (t.queryType().equals(TypeFactory.intSort)) return new Exp.I(getIntegerVariableFor(x));
      if (t.queryType().equals(TypeFactory.boolSort)) return new Exp.B(getBooleanVariableFor(x));
      if (t.queryType().equals(TypeFactory.stringSort)) return new Exp.S(getStringVariableFor(x));
      throw new UnsupportedTheoryException(t.toString(), "variable has type " + t.queryType() +
        " which can neither be translated to an SMT expression nor to a constraint");
    }
    if (t.isValue()) {
      Value v = t.toValue();
      if (v.isIntegerValue()) return new Exp.I(SmtFactory.createValue(v.getInt()));
      if (v.isStringValue()) return new Exp.S(SmtFactory.createValue(v.getString()));
      if (v.isBooleanValue()) return new Exp.B(SmtFactory.createValue(v.getBool()));
      throw new UnsupportedTheoryException(t.toString(), "unsupported value " + t.isValue() +
        " (only integer values and boolean values are supported in the SMT solver");
    }
    CalculationSymbol calc = getCalculationRoot(t);
    return switch (calc.queryKind()) {
      case CalculationSymbol.Kind.MINUS -> {
        assertArgumentCount(t, 1);
        yield new Exp.I(SmtFactory.createNegation(translateIntegerExpression(t.queryArgument(1))));
      }
      case CalculationSymbol.Kind.PLUS -> {
        assertArgumentCount(t, 2);
        yield new Exp.I(SmtFactory.createAddition(translateIntegerExpression(t.queryArgument(1)),
                                                  translateIntegerExpression(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.TIMES -> {
        assertArgumentCount(t, 2);
        yield new Exp.I(SmtFactory.createMultiplication(translateIntegerExpression(t.queryArgument(
                                              1)), translateIntegerExpression(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.DIV -> {
        assertArgumentCount(t, 2);
        yield new Exp.I(SmtFactory.createDivision(translateIntegerExpression(t.queryArgument(1)),
                                                  translateIntegerExpression(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.MOD -> {
        assertArgumentCount(t, 2);
        yield new Exp.I(SmtFactory.createModulo(translateIntegerExpression(t.queryArgument(1)),
                                                 translateIntegerExpression(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.GREATER -> {
        assertArgumentCount(t, 2);
        yield new Exp.B(SmtFactory.createGreater(translateIntegerExpression(t.queryArgument(1)),
                                                 translateIntegerExpression(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.SMALLER -> {
        assertArgumentCount(t, 2);
        yield new Exp.B(SmtFactory.createSmaller(translateIntegerExpression(t.queryArgument(1)),
                                                 translateIntegerExpression(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.GEQ -> {
        assertArgumentCount(t, 2);
        yield new Exp.B(SmtFactory.createGeq(translateIntegerExpression(t.queryArgument(1)),
                                              translateIntegerExpression(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.LEQ -> {
        assertArgumentCount(t, 2);
        yield new Exp.B(SmtFactory.createLeq(translateIntegerExpression(t.queryArgument(1)),
                                             translateIntegerExpression(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.EQUALS -> {
        assertArgumentCount(t, 2);
        if (t.queryArgument(1).queryType().equals(TypeFactory.intSort)) {
          yield new Exp.B(SmtFactory.createEqual(translateIntegerExpression(t.queryArgument(1)),
                                                 translateIntegerExpression(t.queryArgument(2))));
        }
        else {
          yield new Exp.B(SmtFactory.createEqual(translateStringExpression(t.queryArgument(1)),
                                                 translateStringExpression(t.queryArgument(2))));
        }
      }
      case CalculationSymbol.Kind.NEQ -> {
        assertArgumentCount(t, 2);
        if (t.queryArgument(1).queryType().equals(TypeFactory.intSort)) {
          yield new Exp.B(SmtFactory.createUnequal(translateIntegerExpression(t.queryArgument(1)),
                                                   translateIntegerExpression(t.queryArgument(2))));
        }
        else {
          yield new Exp.B(SmtFactory.createUnequal(translateStringExpression(t.queryArgument(1)),
                                                   translateStringExpression(t.queryArgument(2))));
        }
      }
      case CalculationSymbol.Kind.AND -> {
        assertArgumentCount(t, 2);
        yield new Exp.B(SmtFactory.createConjunction(translateConstraint(t.queryArgument(1)),
                                                     translateConstraint(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.OR -> {
        assertArgumentCount(t, 2);
        yield new Exp.B(SmtFactory.createDisjunction(translateConstraint(t.queryArgument(1)),
                                                     translateConstraint(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.NOT -> {
        assertArgumentCount(t, 1);
        yield new Exp.B(SmtFactory.createNegation(translateConstraint(t.queryArgument(1))));
      }
      case CalculationSymbol.Kind.IFF -> {
        assertArgumentCount(t, 2);
        yield new Exp.B(SmtFactory.createIff(translateConstraint(t.queryArgument(1)),
                                             translateConstraint(t.queryArgument(2))));
      }
      case CalculationSymbol.Kind.XOR -> {
        assertArgumentCount(t, 2);
        yield new Exp.B(SmtFactory.createIff(translateConstraint(t.queryArgument(1)),
                                             translateConstraint(t.queryArgument(2))).negate());
      }
    };
  }

  /** This function throws an UnsupportedTheoryException if t.numberArguments() is not numArgs. */
  private void assertArgumentCount(Term t, int numArgs) {
    if (t.numberArguments() != numArgs) throw new UnsupportedTheoryException(t.toString(),
      "Expected " + t.queryRoot().toString() + " (of kind " +
      t.queryRoot().toCalculationSymbol().queryKind() + ") to take " + numArgs + " arguments, " +
      "not " + t.numberArguments() + ".");
  }

  /**
   * This takes a theory term of type Int, and returns the corresponding IntegerExpression, for use
   * in SMT analysis.
   *
   * Note that calling this function has side effects, in that SMT variables are generated for all
   * the variables in t, and are stored.  If you use two different TermSmtTranslators to translate
   * the same term, you may not get the same IntegerExpression out because variables might be
   * renamed.
   */
  public IntegerExpression translateIntegerExpression(Term t) {
    switch (translate(t)) {
      case Exp.I(IntegerExpression e): return e;
      default: throw new TypingException("TermSmtTranslator", "translateIntegerExpression",
        t.toString(), t.queryType().toString(), "Int");
    }
  }

  /**
   * This takes a theory term of type String, and returns the corresponding StringExpression, for
   * use in SMT analysis.
   *
   * Note that calling this function has side effects, in that SMT variables are generated for all
   * the variables in t, and are stored.  If you use two different TermSmtTranslators to translate
   * the same term, you may not get the same StringExpression out because variables might be
   * renamed.
   */
  public StringExpression translateStringExpression(Term t) {
    switch (translate(t)) {
      case Exp.S(StringExpression e): return e;
      default: throw new TypingException("TermSmtTranslator", "translateStringExpression",
        t.toString(), t.queryType().toString(), "String");
    }
  }

  /**
   * This takes a theory term of type Bool, and returns the corresponding Constraint, for use in
   * SMT analysis.
   *
   * Note that calling this function has side effects, in that SMT variables are generated for all
   * the variables in t, and are stored.  If you use two different TermSmtTranslators to translate
   * the same term, you may not get the same Constraint out because variables might be renamed.
   */
  public Constraint translateConstraint(Term t) {
    switch (translate(t)) {
      case Exp.B(Constraint c): return c;
      default: throw new TypingException("TermSmtTranslator", "translateConstraint",
        t.toString(), t.queryType().toString(), "Bool");
    }
  }

  /**
   * Assuming that t is a theory term of type Bool, this adds the corresponding Constraint to the
   * underlying SmtProblem.
   */
  public void require(Term t) {
    _problem.require(translateConstraint(t));
  }

  /**
   * Assuming that both premise and conclusion are theory terms of type Bool, this adds the
   * Constraint corresponding to "premise ⇒ conclusion" to the underlying SmtProblem.
   */
  public void requireImplication(Term premise, Term conclusion) {
    _problem.requireImplication(translateConstraint(premise), translateConstraint(conclusion));
  }
}

