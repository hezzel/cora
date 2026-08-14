/**************************************************************************************************
 Copyright 2019--2026 Cynthia Kop

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

import java.lang.Comparable;
import charlie.types.Type;

/**
 * <p>FunctionSymbols are the primary ingredient to construct terms.</p>
 *
 * <p>Function symbols are defined by (1) their name, (2) their type, and (3) a "special" field
 * that indicates what sort of symbol this is.  For example, the special field could indicate that a
 * symbol is a temporary fresh copy of a symbol used in analysis, or that it belongs to a theory.
 * </p>
 *
 * <p>Note that function symbol equality is defined by the combination of the three points above.
 * Hence, function symbols may be overloaded: the same name occurring with different types; this
 * is in principle a different symbol.</p>
 *
 * <p>Note: all instances of FunctionSymbol must (and can be expected to) be immutable.</p>
 */
public interface FunctionSymbol extends Term, Comparable<FunctionSymbol> {
  /**
   * All function symbols have a name that identifies how they are printed.
   * They are not necessarily identified uniquely by their name.
   */
  String queryName();

  /** <p>All function symbols have a type, which restricts how the symbol can be applied.</p> */
  Type queryType();

  /**
   * Function symbols have a (possibly empty) "special" field, which is used to group symbols of
   * specific kinds.  Basic user-defined function symbols have special set to the empty string "".
   */
  String querySpecial();

  /** Returns the number of arguments that this function symbol can (at most) be applied to. */
  int queryArity();

  /**
   * <p>Included for use by the printer: this returns if the symbol should be printed in infix
   * notation by default.  (Custom printers may make their own infix choices.)</p>
   *
   * <p>Infix symbols are not required to be binary: they may have any arity ≥ 1.  The immediate
   * consequences for printing an infix symbol of arity n are (by default):</p>
   * <li>if an infix symbol occurs with too few arguments, so f(s1,...,sk) with k < n, then it is
   *   printed in the usual functional notation but the symbol f may be printed differently, e.g.,
   *   [f](s1,...,sk)</li>
   * <li>if an infix symbol occurs fully applied and n = 1, so f(s), then it is printed as f s
   *   (with brackets around s only if needed according to queryIncludeBrackets)</li>
   * <li>if an infix symbol occurs fully applied and n ≥ 2, so f(s1,...,sn), then it is printed
   *   in an infix notation, so s1 f ... f sn</li>
   *
   * <p>Alternative term printers may deal with infix symbols differently or ignore infix notation
   * altogether!</p>
   */
  boolean isInfixSymbol();

  /**
   * <p>In case of an infix symbol, this method is used to handle associativity and priority: given
   * that argument [argument] is rooted by the infix symbol [below], it returns whether brackets
   * should be printed around this argument if we're using standard infix notation.</p>
   *
   * <p>Arguments are counted from 1, so in s # t, queryIncludeBrackets(s.queryRoot(), 1) and
   * queryIncludeBrackets(t.queryRoot(), 2) would be called.</p>
   *
   * <p>This defaults to true, so for non-infix symbols it is not necessary to supply this
   * method.</p>
   */
  default boolean queryIncludeBrackets(FunctionSymbol below, int argument) {
    return true;
  }

  /**
   * Returns whether the current symbol is equal to another.
   * This is the case if they have the same name, typing and special property.
   */
  boolean equals(FunctionSymbol other);

  /**
   * ONLY RELEVANT FOR POLYMORPHIC FUNCTION SYMBOLS: this function returns a copy of the current
   * function symbol with the type substituted according to the given type mapping.
   */
  FunctionSymbol substituteType(Type.ISubstitution typeMapping);

  /**
   * <p>ONLY RELEVANT FOR POLYMORPHIC FUNCTION SYMBOLS: this function tries to extend typeMapping
   * so that this.substituteType(typeSubstitution) equals instance.  If successful, true is
   * returned (and typeMapping is fully updated as needed).  If unsuccessful, false is returned,
   * but it is possible that typeMapping is still changed.</p>
   *
   * <p>Since the given map is meant to be updated, it should be a mutable map.  The map is
   * guaranteed to only be extended (and only with type variables that occur inside the type of the
   * current function symbol), not changed in any other way.</p>
   */
  boolean match(FunctionSymbol instance, Type.MSubstitution typeSubstitution);
}

