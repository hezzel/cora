/*************************************************************************************************
 Copyright 2019, 2022 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rewriting;

import java.util.List;
import cora.exceptions.IllegalRuleError;
import cora.exceptions.IllegalSymbolError;
import cora.terms.FunctionSymbol;

/**
 * An MSTRS (many-sorted term rewriting system) is a _first-order_ TRS.  Despite the name, it is
 * not mandatory for there to be many sorts; one is enough.  In an MSTRS, the only rules are
 * non-polymorphic, first-order rules; there are no rule schemes.
 */
public class MSTRS extends TRS {
  /** Create a TRS with the given alphabet and rules. */
  public MSTRS(Alphabet alphabet, List<Rule> rules) {
    super(alphabet, rules);

    // assert that everything in the alphabet is first-order
    for (FunctionSymbol f : alphabet.getSymbols()) {
      if (f.queryType().queryTypeOrder() > 1) {
        throw new IllegalSymbolError("MSTRS", f.toString(), "Symbol with a type " +
          f.queryType().toString() + " cannot occur in a many-sorted TRS.");
      }
    }

    // assert that all the rules are first-order
    for (Rule rule : rules) {
      if (!rule.isFirstOrder()) {
        throw new IllegalRuleError("MSTRS", "Rule " + rule.toString() + " cannot ocucr in a " +
          "many-sorted TRS, as it is not first-order.");
      }
    }
  }
}

