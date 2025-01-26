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

package cora.rwinduction.engine;

import charlie.types.Type;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.terms.TermFactory;

/**
 * Several deduction rules introduce fresh variables.  This class is used to come up with suitable
 * names for these variables, taking into account their origin and the naming of variables in the
 * TRS rules.
 */
public class VariableNamer {
  public record VariableInfo(String basename, int index) {}

  /**
   * Given a variable with name [baseName], that is called [fullName] in a renaming, this
   * interprets the variable as a combination of name and index.  This might just be
   * ([fullName],0), but especially if the variable was created by the VariableNamer, there could
   * be a clearer division.
   */
  public VariableInfo getVariableInfo(String baseName, String fullName) {
    int index = fullName.length();
    while (index > 0 && Character.isDigit(fullName.charAt(index-1))) index--;
    int num = 0;
    if (index != fullName.length()) {
      num = Integer.parseInt(fullName.substring(index));
      fullName = fullName.substring(0, index);
    }
    String base = fullName;
    if (baseName.length() < fullName.length() &&
        fullName.substring(0,baseName.length()).equals(baseName)) base = baseName;
    return new VariableInfo(base, num);
  }

  /**
   * For creating a new variable that is derived from x (for example, it's one of the variables
   * needed in a case analysis on x), this function returns an appropriate base name and index,
   * so that <basename><index> does not occur in the given renaming.
   */
  public VariableInfo chooseDerivativeNaming(Variable x, Renaming renaming) {
    String basename = x.queryName();
    String fullname = renaming.getName(x);
    if (fullname == null) fullname = basename;
    VariableInfo current = getVariableInfo(basename, fullname);
    for (int i = current.index + 1; ; i++) {
      String suggestedName = current.basename() + i;
      if (renaming.isAvailable(suggestedName)) return new VariableInfo(current.basename(), i);
    }
  }
  
  /**
   * This function creates a new variable of the given type, whose name is chosen as a derivative
   * of x (for example, if x is named var203, then the new variable will be named var204).  The new
   * variable will be immediately stored in the renaming.
   */
  public Variable chooseDerivative(Variable x, Renaming renaming, Type type) {
    VariableInfo info = chooseDerivativeNaming(x, renaming);
    Variable newvar = TermFactory.createVar(info.basename(), type);
    renaming.setName(newvar, info.basename() + info.index());
    return newvar;
  }
}

