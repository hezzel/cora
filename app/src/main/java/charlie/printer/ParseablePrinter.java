/**************************************************************************************************
 Copyright 2025 Cynthia Kop

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

import charlie.types.Type;
import charlie.types.TypePrinter;
import charlie.terms.Replaceable;
import charlie.terms.Renaming;
import charlie.terms.TermPrinter;
import charlie.terms.position.PositionPrinter;
import charlie.trs.Rule;

/**
 * The ParseablePrinter prints with only standard characters, and in such a way as to make the
 * result parseable where possible
 */
public class ParseablePrinter extends AsciiPrinter{
  public ParseablePrinter(TypePrinter ty, PositionPrinter po, TermPrinter te) {
    super(ty, po, te);
  }

  /** Stores the declaration for the given rule in the builder. */
  private void printDeclaration(Replaceable x, Renaming renaming) {
    _builder.append(renaming.getName(x));
    _builder.append(" :: ");
    Type type = x.queryType();
    if (x.queryReplaceableKind() == Replaceable.KIND_METAVAR) {
      _builder.append("[");
      for (int i = 0; i < x.queryArity(); i++) {
        if (i > 0) _builder.append(", ");
        _typePrinter.print(type.subtype(1), _builder);
        type = type.subtype(2);
      }
      _builder.append("] -> ");
    }
    _typePrinter.print(type, _builder);
  }

  /**
   * This prints the rule including a declaration of all variables and meta-variables occurring in
   * it, e.g., { F :: [Int, Bool] -> A, x :: Int } g(\y::Bool.F[x,y]) -> F[x,true].
   */
  protected void printRule(Rule rho, Renaming renaming) {
    Set<Replaceable> replaceables;
    if (renaming == null) {
      renaming = _termPrinter.generateUniqueNaming(rho.queryLeftSide(), rho.queryRightSide(),
                                                   rho.queryConstraint());
      replaceables = renaming.domain();
    }
    else replaceables = rho.queryAllReplaceables();

    _builder.append("{ ");
    boolean first = true;
    for (Replaceable x : replaceables) {
      if (first) first = false;
      else _builder.append(", ");
      printDeclaration(x, renaming);
    }
    if (!first) _builder.append(" ");
    _builder.append("} ");
    super.printRule(rho, renaming);
  }
}

