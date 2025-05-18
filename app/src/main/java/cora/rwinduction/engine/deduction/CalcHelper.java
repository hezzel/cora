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

package cora.rwinduction.engine.deduction;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Optional;
import java.util.Stack;

import charlie.terms.*;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This class contains a number of static functions for use by the Calc and CalcAll commands.
 */
final class CalcHelper {
  /**
   * This function checks if the given term satisfies the prerequisites of the calc rule: it is a
   * first-order theory term, so any value instantiation can be reduced using the calculation step
   * to a value.
   */
  static boolean calculatable(Term term) {
    return term.isFunctionalTerm() &&
           term.isApplication() &&
           term.isTheoryTerm() &&
           term.isFirstOrder();
  }

  /**
   * This function takes a constraint of the form φ1 ∧...∧ φn, and for every φi of the form
   * x = t or t = x, it stores [t ⇒ x] in the resulting hashmap.  This allows us to recognise
   * calculatable terms that are already defined in the constraint of the equation, and that can
   * thus be rewritten to the existing defining variable.
   */
  static HashMap<Term,Variable> breakupConstraint(Term constraint) {
    HashMap<Term,Variable> ret = new HashMap<Term,Variable>();
    Stack<Term> todo = new Stack<Term>();
    todo.push(constraint);
    while (!todo.isEmpty()) {
      Term term = todo.pop();
      while (term.isFunctionalTerm() && term.queryRoot().equals(TheoryFactory.andSymbol) &&
             term.numberArguments() == 2) {
        todo.push(term.queryArgument(2));
        term = term.queryArgument(1);
      }
      if (!term.isFunctionalTerm() || term.numberArguments() != 2) continue;
      CalculationSymbol f = term.queryRoot().toCalculationSymbol();
      if (f == null) continue;
      if (f.queryKind() != CalculationSymbol.Kind.EQUALS &&
          f.queryKind() != CalculationSymbol.Kind.IFF) continue;
      if (term.queryArgument(1).isVariable() && !term.queryArgument(2).isVariable()) {
        ret.put(term.queryArgument(2), term.queryArgument(1).queryVariable());
      }
      if (term.queryArgument(2).isVariable() && !term.queryArgument(1).isVariable()) {
        ret.put(term.queryArgument(1), term.queryArgument(2).queryVariable());
      }
    }
    return ret;
  }

  /**
   * This function chooses a base name for a variable that is meant to replace the given term.
   * The real name (that should be added to the naming) should have the form <base><index>.
   */
  static String chooseBaseName(Term term) {
    if (term.freeReplaceables().size() == 1) {
      for (Replaceable x : term.freeReplaceables()) return x.queryName();
    }
    return term.queryType().toString().substring(0,1).toLowerCase();
  }
}

