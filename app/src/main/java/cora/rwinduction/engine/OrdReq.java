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

package cora.rwinduction.engine;

import charlie.util.Pair;
import charlie.terms.Term;

/**
 * A requirement that left ≻ right under some condition.
 * This really is stub code, to design ProofState as it will eventually be needed.  Expand (and do
 * proper testing / renamings) when ordering requirements are added!
 */
public class OrdReq {
  private Term _lhs;
  private Term _rhs;
  private Term _constraint;

  public OrdReq(Term left, Term right, Term constraint) {
    _lhs = left;
    _rhs = right;
    _constraint = constraint;
  }

  public String toString() {
    return _lhs.toString() + " ≻ " + _rhs.toString() + " | " + _constraint.toString();
  }
}

