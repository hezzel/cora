/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

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

import java.util.List;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.substitution.MutableSubstitution;

/** This class implements the beta rule scheme. */
class BetaReducer implements ReduceObject {
  public boolean applicable(Term t) {
    return t.isBetaRedex();
  }

  public Term apply(Term t) {
    Term head = t.queryHead();
    List<Term> args = t.queryArguments();
    if (!head.isAbstraction() || args.size() < 1) return null;
    Term a = head.queryAbstractionSubterm();
    Variable x = head.queryVariable();
    Term b = args.get(0);
    MutableSubstitution gamma = new MutableSubstitution();
    gamma.extend(x, b);
    Term newhead = gamma.substitute(a);
    if (args.size() == 1) return newhead;
    return newhead.apply(args.subList(1, args.size()));
  }

  public String toString() {
    return "β : (λx.s)(t_0,...,t_n) → s[x:=t_0](t_1,...,t_n)";
  }
}

