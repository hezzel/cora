/**************************************************************************************************
 Copyright 2022-2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import java.util.Set;
import java.util.HashSet;
import charlie.types.*;
import charlie.terms.CalculationSymbol.Kind;
import charlie.terms.CalculationSymbol.Associativity;

/**
 * A factory only to create logical terms and symbols
 *
 * Note: all theory symbols (values and calculation symbols) necessarily have a translation in
 * SMT.  Thus, when adding any function symbol here, also add them into the translator functionality
 * in smt.TermSmtTranslator and smt.TermAnalyser.
 */
public class TheoryFactory {
  private static Type binaryIntOperatorType = TypeFactory.createArrow(TypeFactory.intSort,
    TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.intSort));
  private static Type binaryIntComparisonType = TypeFactory.createArrow(TypeFactory.intSort,
    TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.boolSort));
  private static Type binaryStringComparisonType = TypeFactory.createArrow(TypeFactory.stringSort,
    TypeFactory.createArrow(TypeFactory.stringSort, TypeFactory.boolSort));
  private static Type binaryBoolConnectiveType = TypeFactory.createArrow(TypeFactory.boolSort,
    TypeFactory.createArrow(TypeFactory.boolSort, TypeFactory.boolSort));

  /** Create a non-binder variable with the given name and base sort. */
  public static Variable createVar(String name, Base type) {
    if (!type.isTheoryType()) {
      throw new IllegalArgumentException("TheoryFactory::createVar is given type " + type +
        " which is not a theory sort.");
    }
    return new Var(name, type);
  }

  /** Create a non-binder boolean variable with the given name. */
  public static Variable createBoolVar(String name) {
    return new Var(name, TypeFactory.boolSort);
  }

  /** Create a non-binder integer variable with the given name. */
  public static Variable createIntVar(String name) {
    return new Var(name, TypeFactory.intSort);
  }

  /** Create an Integer Value */
  public static Value createValue(int n) {
    return new IntegerValue(n);
  }

  /** Create a Boolean Value */
  public static Value createValue(boolean b) {
    return new BooleanValue(b);
  }

  /** Create a String Value */
  public static Value createValue(String s) {
    return new StringValue(s);
  }

  /** Create a String Value with a string in quotes, and potentially with escape characters in it */
  public static Value createEscapedStringValue(String s) throws IncorrectStringException {
    return StringValue.parseUserStringValue(s);
  }

  /**
   * Create an equality between two terms of the same theory sort.
   * If they do not have the same type, or their type is not a (known) theory sort, an
   * IllegalArgumentException will be thrown.
   */
  public static Term createEquality(Term a, Term b) {
    if (!a.queryType().equals(b.queryType())) {
      throw new IllegalArgumentException("TheoryFactory::createEquality received terms of two " +
        "different types!");
    }
    if (a.queryType().equals(TypeFactory.boolSort)) {
      return new Application(iffSymbol, a, b);
    }
    if (a.queryType().equals(TypeFactory.intSort)) {
      return new Application(intEqualSymbol, a, b);
    }
    if (a.queryType().equals(TypeFactory.stringSort)) {
      return new Application(stringEqualSymbol, a, b);
    }
    throw new IllegalArgumentException("Cannot create an equality for terms of type " +
      a.queryType().toString());
  }

  /**
   * Creates a conjunction between the two given terms of boolean sort.
   * If they do not have boolean sort, a TypeException is thrown instead.
   */
  public static Term createConjunction(Term a, Term b) {
    if (!a.queryType().equals(TypeFactory.boolSort) || !b.queryType().equals(TypeFactory.boolSort)) {
      throw new IllegalArgumentException("TheoryFactory::createConjunction called with arguments " +
        "of type " + a.queryType().toString() + " and " + b.queryType().toString() +
        " respectively (expected booleans).");
    }
    if (a instanceof BooleanValue) {
      if (((BooleanValue)a).getBool()) return b;
      else return a;
    }
    if (b instanceof BooleanValue) {
      if (((BooleanValue)b).getBool()) return a;
      else return b;
    }
    return new Application(andSymbol, a, b);
  }

  /** The binary symbol for addition */
  public static final CalculationSymbol plusSymbol = new CalculationConstant("+",
    binaryIntOperatorType, Kind.PLUS, Associativity.ASSOC_LEFT, CalculationSymbol.INFIX_PLUS);

  /** The binary symbol for multiplication */
  public static final CalculationSymbol timesSymbol = new CalculationConstant("*",
    binaryIntOperatorType, Kind.TIMES, Associativity.ASSOC_LEFT, CalculationSymbol.INFIX_TIMES);
  
  /** The unary(!) symbol for integer negation */
  public static final CalculationSymbol minusSymbol = new CalculationConstant("-",
    TypeFactory.createArrow(TypeFactory.intSort, TypeFactory.intSort), Kind.MINUS,
    Associativity.NOT_INFIX, CalculationSymbol.INFIX_NONE);

  /** The binary symbol for division */
  public static final CalculationSymbol divSymbol = new CalculationConstant("/",
    binaryIntOperatorType, Kind.DIV, Associativity.ASSOC_NONE, CalculationSymbol.INFIX_DIVMOD);

  /** The binary symbol for modulo */
  public static final CalculationSymbol modSymbol = new CalculationConstant("%",
    binaryIntOperatorType, Kind.MOD, Associativity.ASSOC_NONE, CalculationSymbol.INFIX_DIVMOD);

  /** The binary calculation symbol for conjunction */
  public static final CalculationSymbol andSymbol = new CalculationConstant("∧",
    binaryBoolConnectiveType, Kind.AND, Associativity.ASSOC_LEFT, CalculationSymbol.INFIX_ANDOR);

  /** The binary calculation symbol for disjunction */
  public static final CalculationSymbol orSymbol = new CalculationConstant("∨",
    binaryBoolConnectiveType, Kind.OR, Associativity.ASSOC_LEFT, CalculationSymbol.INFIX_ANDOR);

  /** The unary calculation symbol for boolean negation */
  public static final CalculationSymbol notSymbol = new CalculationConstant("¬",
    TypeFactory.createArrow(TypeFactory.boolSort, TypeFactory.boolSort), Kind.NOT,
    Associativity.NOT_INFIX, CalculationSymbol.INFIX_NONE);

  /** The binary calculation symbol for if and only if */
  public static final CalculationSymbol iffSymbol = new CalculationConstant("⇔",
    binaryBoolConnectiveType, Kind.IFF, Associativity.ASSOC_NONE, CalculationSymbol.INFIX_IFF);

  /** The binary calculation symbol for xor */
  public static final CalculationSymbol xorSymbol = new CalculationConstant("⊻",
    binaryBoolConnectiveType, Kind.XOR, Associativity.ASSOC_NONE, CalculationSymbol.INFIX_XOR);

  /** The binary calculation symbol for greater */
  public static final CalculationSymbol greaterSymbol = new CalculationConstant(">",
    binaryIntComparisonType, Kind.GREATER, Associativity.ASSOC_NONE,
    CalculationSymbol.INFIX_COMPARISON);

  /** The binary calculation symbol for smaller. */
  public static final CalculationSymbol smallerSymbol = new CalculationConstant("<",
    binaryIntComparisonType, Kind.SMALLER, Associativity.ASSOC_NONE,
    CalculationSymbol.INFIX_COMPARISON);

  /** The binary calculation symbol for greater-than-or-equal-to */
  public static final CalculationSymbol geqSymbol = new CalculationConstant("≥",
    binaryIntComparisonType, Kind.GEQ, Associativity.ASSOC_NONE,
    CalculationSymbol.INFIX_COMPARISON);

  /** The binary calculation symbol for smaller-than-or-equal-to */
  public static final CalculationSymbol leqSymbol = new CalculationConstant("≤",
    binaryIntComparisonType, Kind.LEQ, Associativity.ASSOC_NONE,
    CalculationSymbol.INFIX_COMPARISON);

  /** The binary calculation symbol for integer equality */
  public static final CalculationSymbol intEqualSymbol = new CalculationConstant("=",
    binaryIntComparisonType, Kind.EQUALS, Associativity.ASSOC_NONE,
    CalculationSymbol.INFIX_COMPARISON);

  /** The binary calculation symbol for string inequality */
  public static final CalculationSymbol intDistinctSymbol = new CalculationConstant("≠",
    binaryIntComparisonType, Kind.NEQ, Associativity.ASSOC_NONE,
    CalculationSymbol.INFIX_COMPARISON);

  /** The binary calculation symbol for string equality */
  public static final CalculationSymbol stringEqualSymbol = new CalculationConstant("=",
    binaryStringComparisonType, Kind.EQUALS, Associativity.ASSOC_NONE,
    CalculationSymbol.INFIX_COMPARISON);

  /** The binary calculation symbol for inequality */
  public static final CalculationSymbol stringDistinctSymbol = new CalculationConstant("≠",
    binaryStringComparisonType, Kind.NEQ, Associativity.ASSOC_NONE,
    CalculationSymbol.INFIX_COMPARISON);

  /** The value for truth */
  public static final Value trueValue = new BooleanValue(true);
  /** The value for falsehood */
  public static final Value falseValue = new BooleanValue(false);
  /** The value for 0 */
  public static final Value zeroValue = new IntegerValue(0);
  /** The value for the empty string */
  public static final Value emptyStringValue = new StringValue("");

  /** This returns the set of all calculation symbols that are currently supported. */
  public static HashSet<CalculationSymbol> queryAllCalculationSymbols() {
    HashSet<CalculationSymbol> set = new HashSet<CalculationSymbol>();
    set.add(plusSymbol);
    set.add(timesSymbol);
    set.add(minusSymbol);
    set.add(divSymbol);
    set.add(modSymbol);
    set.add(andSymbol);
    set.add(orSymbol);
    set.add(notSymbol);
    set.add(iffSymbol);
    set.add(xorSymbol);
    set.add(greaterSymbol);
    set.add(smallerSymbol);
    set.add(geqSymbol);
    set.add(leqSymbol);
    set.add(intEqualSymbol);
    set.add(intDistinctSymbol);
    set.add(stringEqualSymbol);
    set.add(stringDistinctSymbol);
    return set;
  }

  /** This returns an IntegerValue not included in the given set. */
  public static Value getNewIntValue(Set<Value> exclude) {
    if (!exclude.contains(zeroValue)) return zeroValue;
    for (int i = 1; ; i++) {
      for (int j = 1; j > -2; j -= 2) {
        Value v = new IntegerValue(i * j);
        if (!exclude.contains(v)) return v;
      }
    }
  }

  public static Value getNewStringValue(Set<Value> exclude) {
    if (!exclude.contains(emptyStringValue)) return emptyStringValue;
    for (int i = 1; ; i++) {
      StringBuilder builder = new StringBuilder();
      int k = i;
      while (k > 0) {
        builder.append( (char)((k-1) % 26 + 'a') );
        if (k <= 26) break;
        k = (k - 1) / 26;
      }
      Value v = new StringValue(builder.toString());
      if (!exclude.contains(v)) return v;
    }
  }

  /**
   * This returns a value of the given sort which does not occur in exclude, provided one exists
   * (for infinite sorts, like Int or String, one always exists).  If there is no such value then
   * null is returned instead.  Note that if sort is not a theory sort, then null is always
   * returned.
   */
  public static Value getNewValue(Base sort, Set<Value> exclude) {
    if (sort.equals(TypeFactory.boolSort)) {
      if (!exclude.contains(trueValue)) return trueValue;
      if (!exclude.contains(falseValue)) return falseValue;
      return null;
    }
    if (sort.equals(TypeFactory.intSort)) return getNewIntValue(exclude);
    if (sort.equals(TypeFactory.stringSort)) return getNewStringValue(exclude);
    return null;
  }
}

