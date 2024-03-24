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

package cora.io;

import java.util.Set;
import charlie.types.TypePrinter;
import charlie.terms.TermPrinter;
import charlie.terms.CalculationSymbol;
import charlie.terms.CalculationSymbol.Kind;

/** The PlainTermPrinter adapts the standard TermPrinter to avoid unicode symbols. */
public class PlainTermPrinter extends TermPrinter {
  public PlainTermPrinter(TypePrinter typr, Set<String> avoid) {
    super(typr, avoid);
  }

  protected String queryTupleOpenBracket() { return "(|"; }
  protected String queryTupleCloseBracket() { return "|)"; }
  protected String queryLambda() { return "\\"; }
  protected String queryMetaOpenBracket() { return "["; }
  protected String queryMetaCloseBracket() { return "]"; }

  protected String queryCalculationName(Kind symbolkind, String defaultName) {
    return switch (symbolkind) {
      case Kind.AND -> "/\\";
      case Kind.OR -> "\\/";
      case Kind.GREATER -> ">";
      case Kind.SMALLER -> "<";
      case Kind.GEQ -> ">=";
      case Kind.LEQ -> "<=";
      case Kind.EQUALS -> "=";
      case Kind.NEQ -> "!=";
      case Kind.NOT -> "not ";
      case Kind.PLUS -> "+";
      case Kind.TIMES -> "*";
      case Kind.DIV -> "/";
      case Kind.MOD -> "%";
      case Kind.MINUS -> "-";
    };
  }
}

