/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.types;

import charlie.util.FixedList;

/**
 * TypePrinters are used in the overall output process of the tool.  This class provides a default
 * implementation, but is meant to be inherited.  You can for instance instantiate the type printer
 * to use unicode symbols, ascii-art, html, print smt-style or whatever is needed.
 */
public class TypePrinter {
  /**
   * Returns a string representation of the given type (using the other print method).
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final String print(Type t) {
    StringBuilder builder = new StringBuilder();
    print(t, builder);
    return builder.toString();
  }

  /**
   * This is the main public access function.  Call this to ensure that the given type is printed
   * to the given string builder.
   * 
   * To define your own TypePrinter, you can either override this method directly -- in which
   * case there is no need to override any of the other methods in the class -- or override (some
   * of) the functions it calls, which are printBaseType, printArrowType and printProductType,
   * directly.
   */
  public void print(Type t, StringBuilder builder) {
    switch (t) {
      case Base(String name): printBaseType(name, builder); break;
      case Arrow(Type left, Type right): printArrowType(left, right, builder); break;
      case Product(FixedList<Type> elems): printProductType(elems, builder); break;
    }
  }

  /**
   * Override this function to change how base types are printed (if printType is left unmasked).
   * The default functionality is just to add the name to the string builder unmodified.
   */
  protected void printBaseType(String name, StringBuilder builder) {
    builder.append(name);
  }

  /**
   * Override this function to change how arrow types are printed (if printType is left unmasked).
   * The default functionality is to print <bracketed left> <type arrow> <unbracketed right>.  If
   * you only want to change the type arrow, override the function queryArrowSymbol() instead.
   */
  protected void printArrowType(Type left, Type right, StringBuilder builder) {
    if (left.isArrowType()) builder.append("(");
    print(left, builder);
    if (left.isArrowType()) builder.append(")");
    builder.append(" ");
    builder.append(queryArrowSymbol());
    builder.append(" ");
    print(right, builder);
  }

  /**
   * Override this function to change how product types are printed (if printType is left
   * unmasked).
   * The default functionality is to print queryTupleOpenBracket(), then all all items in the list
   * separated by commas, and finally queryTupleCloseBracket().
   * If you only want to change the brackets, override the functions queryTupleOpenBracket() and
   * queryTupleCloseBracket() instead.
   */
  protected void printProductType(FixedList<Type> elems, StringBuilder builder) {
    builder.append(queryTupleOpenBracket() + " ");
    for (int i = 0; i < elems.size(); i++) {
      if (i > 0) builder.append(", ");
      print(elems.get(i), builder);
    }   
    builder.append(" " + queryTupleCloseBracket());
  }

  /**
   * Override this function to change how the type arrow is printed if both printType and
   * printArrowType are left unmasked.
   * The default functionality is a unicode arrow.
   */
  protected String queryArrowSymbol() { return "→"; }

  /**
   * Override this function to change how the opening bracket for products is printed if both
   * printType and printProductType are left unmasked.
   * The default functionality is the unicode symbol ⦇.
   */
  protected String queryTupleOpenBracket() { return "⦇"; }

  /**
   * Override this function to change how the jlosing bracket for products is printed if both
   * printType and printProductType are left unmasked.
   * The default functionality is the unicode symbol ⦈.
   */
  protected String queryTupleCloseBracket() { return "⦈"; }
}

