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

package charlie.printer;

import java.util.Set;
import charlie.types.Arrow;
import charlie.types.Type;
import charlie.types.TypePrinter;
import charlie.terms.Variable;
import charlie.terms.TermPrinter;
import charlie.terms.CalculationSymbol;
import charlie.terms.CalculationSymbol.Kind;

/**
 * The ParseableTermPrinter specifically prints terms in such a way that the result can be parsed
 * by the CoraInputReader again.  Beyond that, it is a plain printer; no unicode, just ascii.
 */
public class ParseableTermPrinter extends TermPrinter {
  private TypePrinter _typePrinter;

  public ParseableTermPrinter(Set<String> avoid, TypePrinter typeprint) {
    super(avoid);
    _typePrinter = typeprint;
  }

  public ParseableTermPrinter(Set<String> avoid) {
    super(avoid);
    _typePrinter = new PlainTypePrinter();
  }

  @Override
  protected String queryTupleOpenBracket() { return "(|"; }
  @Override
  protected String queryTupleCloseBracket() { return "|)"; }
  @Override
  protected String queryLambda() { return "\\"; }
  @Override
  protected String queryMetaOpenBracket() { return "["; }
  @Override
  protected String queryMetaCloseBracket() { return "]"; }

  @Override
  protected String queryCalculationName(Kind symbolkind, String defaultName, Type symboltype) {
    return switch (symbolkind) {
      case Kind.IFF -> "<=>";
      case Kind.XOR -> "xor";
      case Kind.AND -> "/\\";
      case Kind.OR -> "\\/";
      case Kind.GREATER -> ">";
      case Kind.SMALLER -> "<";
      case Kind.GEQ -> ">=";
      case Kind.LEQ -> "<=";
      case Kind.EQUALS -> {
        if (symboltype instanceof Arrow(Type a, Type b) &&
            a.isBaseType()) yield "=_" + _typePrinter.print(a);
        else yield "=";   // shouldn't happen
      }
      case Kind.NEQ -> {
        if (symboltype instanceof Arrow(Type a, Type b) &&
            a.isBaseType()) yield "!=_" + _typePrinter.print(a);
        else yield "!=";  // shouldn't happen
      }
      case Kind.NOT -> "not ";
      case Kind.PLUS -> "+";
      case Kind.TIMES -> "*";
      case Kind.DIV -> "/";
      case Kind.MOD -> "%";
      case Kind.MINUS -> "-";
    };
  }

  @Override
  protected void printAbstractionBinder(Variable binder, String chosenName, StringBuilder builder) {
    builder.append(chosenName);
    builder.append(" :: ");
    _typePrinter.print(binder.queryType(), builder);
  }
}

