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

/**
 * SExpPrinters are used in the overall output process of the tool.  This class provides a default
 * implementation, but is meant to be inherited.  You can for instance instantiate the SExpPrinter
 * to use unicode symbols, ascii-art, html, print smt-style or whatever is needed.
 */
public class SExpPrinter {
  /**
   * Returns a string representation of the given StringExpression (using the other print method).
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final String print(StringExpression e) {
    StringBuilder builder = new StringBuilder();
    print(e, builder);
    return builder.toString();
  }

  /**
   * This is the main public access function.  Call this to ensure that the given string expression
   * is printed to the given string builder.
   * 
   * To define your own SExpPrinter, you can either override this method directly -- in which
   * case there is no need to override any of the other methods in the class -- or override (some
   * of) the functions it calls, which are printVar and printValue.
   */
  public void print(StringExpression e, StringBuilder builder) {
    switch (e) {
      case SVar x: printVar(x, builder); break;
      case SValue k: printValue(k, builder); break;
    }
  }

  /**
   * Override this function to change how String variables are printed (if print is left unmasked).
   * The default functionality is just to add the name to the string builder unmodified.
   */
  protected void printVar(SVar x, StringBuilder builder) {
    builder.append(x.queryName());
  }

  /**
   * Override this function to change how String values are printed (if print is left unmasked).
   * The default functionality is to add the SMT description of the value.
   */
  protected void printValue(SValue k, StringBuilder builder) {
    builder.append(SValue.encode(k.queryValue()));
  }
}

