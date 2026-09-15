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

import java.util.List;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.TermFactory;

/** This class implements the eta-shortening rule scheme. */
class EtaReducer implements ReduceObject {
  public boolean applicable(Term t) {
    Term s = t.queryHead();
    if (!s.isAbstraction()) return false;
    Variable x = s.queryVariable();
    Term main = s.queryAbstractionSubterm();
    List<Term> parts = main.listArguments();
    if (parts.size() == 0) return false;
    if (!parts.get(parts.size()-1).equals(x)) return false;
    if (main.queryHead().queryFreeVariables().contains(x)) return false;
    for (int i = 0; i < parts.size()-1; i++) {
      if (parts.get(i).queryFreeVariables().contains(x)) return false;
    }
    return true;
  }

  public Term apply(Term t) {
    Term s = t.queryHead();
    if (!s.isAbstraction()) return null;
    Variable x = s.queryVariable();
    Term main = s.queryAbstractionSubterm();
    Term head = main.queryHead();
    List<Term> args = main.listArguments();
    if (args.size() == 0 || !args.get(args.size()-1).equals(x)) return null;
    args = args.subList(0, args.size()-1);
    Term ret = TermFactory.createApp(head, args);
    if (ret.queryFreeVariables().contains(x)) return null;
    args = t.listArguments();
    if (args.size() > 0) ret = TermFactory.createApp(ret, args);
    return ret;
  }

  public String toString() {
    return "η : λx.s x → x if x ∉ FV(s)";
  }
}

