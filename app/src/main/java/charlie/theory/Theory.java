/**************************************************************************************************
 Copyright 2026 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.theory;

import charlie.types.*;
import charlie.terms.Term;
import charlie.terms.FunctionSymbol;

/**
 * The Theory class carries the knowledge of the theories supported by Cora, and can be used to
 * identify symbols and terms as theory, as well as casting symbols.
 */
public class Theory {
  /**
   * Returns true if the given Type is one of the pre-defined theory base types (e.g., Int,
   * Bool).
   */
  public static boolean isBaseTheoryType(Type type) {
    return
      type == TypeFactory.intSort  ||
      type == TypeFactory.boolSort ||
      type == TypeFactory.stringSort;
  }
  /**
   * Returns true if the given type is built entirely from theory sorts and arrows; type variables
   * and other base and data types are not permitted.
   * Theory sorts are the base types specifically created as theory, accessible from the theory
   * factory.
   */
  public static boolean isTheory(Type type) {
    return switch(type) {
      case Base b -> isBaseTheoryType(b);
      case Arrow a -> isTheory(a.querySubtype(1)) && isTheory(a.querySubtype(2));
      default -> false;
    };
  }

  /** Returns true if the given Term is a Value, false if it is not. */
  public static boolean isValue(Term t) {
    return t instanceof Value;
  }

  /** Returns true if the given Term is an IntegerValue, so a Value of type Int. */
  public static boolean isIntegerValue(Term t) {
    return t instanceof IntegerValue;
  }

  /** Returns true if the given Term is a BooleanValue, so a Value of type Bool. */
  public static boolean isBooleanValue(Term t) {
    return t instanceof BooleanValue;
  }

  /** Returns true if the given Term is a StringValue, so a value of type String. */
  public static boolean isStringValue(Term t) {
    return t instanceof StringValue;
  }

  /** If the given term is a value, returns it; otherwise returns null. */
  public static Value toValue(Term t) {
    if (t instanceof Value v) return v;
    return null;
  }

  /** If the given term is an integer value, returns it; otherwise returns null. */
  public static IntegerValue toIntegerValue(Term t) {
    if (t instanceof IntegerValue v) return v;
    return null;
  }

  /** If the given term is a boolean value, returns it; otherwise returns null. */
  public static BooleanValue toBooleanValue(Term t) {
    if (t instanceof BooleanValue v) return v;
    return null;
  }

  /** If the given term is a string value, returns it; otherwise returns null. */
  public static StringValue toStringValue(Term t) {
    if (t instanceof StringValue v) return v;
    return null;
  }

  /** If the given term is the boolean value "true" this returns true, otherwise false. */
  public static boolean isTrue(Term t) {
    return t instanceof BooleanValue v && v.getBool();
  }

  /** Returns true if the given FunctionSymbol is a calculationSymbol, false if it is not. */
  public static boolean isCalculationSymbol(FunctionSymbol f) {
    return f instanceof CalculationSymbol;
  }

  /** If the given function symbol is a calculation symbol, returns it; otherwise returns null. */
  public static CalculationSymbol toCalculationSymbol(FunctionSymbol f) {
    if (f instanceof CalculationSymbol c) return c;
    return null;
  }

  /** This returns whether the given symbol is a theory symbol: so a value or calculation symbol */
  public static boolean isTheory(FunctionSymbol f) {
    return isValue(f) || isCalculationSymbol(f);
  }

  /**
   * This returns true if the given term is a theory term (also known as logical term).  That is,
   * it is a true term (so no meta-variables other than variables), its function symbols are all
   * theory symbols, and its variables all have a theory type.
   */
  public static boolean isTheory(Term t) {
    if (t.isVariable()) return isTheory(t.queryType());
    if (t.isConstant()) return isValue(t.queryRoot()) || isCalculationSymbol(t.queryRoot());
    if (t.isAbstraction()) {
      return isTheory(t.queryVariable().queryType()) &&
             isTheory(t.queryAbstractionSubterm());
    }
    if (t.isApplication()) {
      if (!isTheory(t.queryHead())) return false;
      for (int i = 1; i <= t.queryNumberArguments(); i++) {
        if (!isTheory(t.queryArgument(i))) return false;
      }
      return true;
    }
    if (t.isMetaApplication()) return false;
    throw new IllegalArgumentException("Theory::isTheory called with a term that does not have " +
      "any of the standard term shapes!");
  }
}

