/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.reduction;

import cora.terms.Term;
import cora.terms.FunctionSymbol;
import cora.theorytranslation.TermAnalyser;

/** This class implements the calculation rule scheme. */
class CalcReducer implements ReduceObject {
  public boolean applicable(Term t) {
    if (!t.queryType().isBaseType() || !t.queryType().isTheoryType()) return false;
    if (!t.isFunctionalTerm()) return false;
    FunctionSymbol root = t.queryRoot();
    if (root == null || !root.isTheorySymbol() || root.isValue()) return false;
    for (int i = 1; i <= t.numberArguments(); i++) {
      if (!t.queryArgument(i).isValue()) return false;
    }
    return true;
  }

  public Term apply(Term t) {
    if (!t.queryType().isBaseType() || !t.queryType().isTheoryType()) return null;
    if (t.isValue() || !t.isGround() || !t.isTheoryTerm()) return null;
    return TermAnalyser.calculate(t);
  }

  public String toString() {
    return "calc : f(x1,...,xk) → y [f(x1,...,xk) = y] for f ∈ Σ_{theory}";
  }
}

