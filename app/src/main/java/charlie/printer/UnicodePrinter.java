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

import charlie.types.TypePrinter;
import charlie.terms.TermPrinter;
import charlie.terms.position.PositionPrinter;

/** The UnicodePrinter prints using unicode symbols -- which is actually the default way. */
public class UnicodePrinter extends Printer {
  public UnicodePrinter(TypePrinter ty, PositionPrinter po, TermPrinter te) {
    super(ty, te, po);
  }

  public String symbRuleArrow()       { return "→"; }
  public String symbTypeArrow()       { return "→"; }
  public String symbMapsto()          { return "↦"; }
  public String symbThickArrow()      { return "➡"; }
  public String symbLongArrow()       { return "⟶"; }
  public String symbDownArrow()       { return "↓"; }
  public String symbRevRuleArrow()    { return "←"; }

  public String symbVdash()           { return "⊢"; }
  public String symbVDash()           { return "⊨"; }
  public String symbForall()          { return "∀"; }
  public String symbExists()          { return "∃"; }
  public String symbAnd()             { return "∧"; }
  public String symbOr()              { return "∨"; }
  public String symbNot()             { return "¬"; }
  public String symbImplies()         { return "⇒"; }

  public String symbEmptySet()        { return "ø"; }
  public String symbUnion()           { return "∪"; }
  public String symbSubterm()         { return "⊲"; }
  public String symbSubtermeq()       { return "⊴"; }
  public String symbSupterm()         { return "⊳"; }
  public String symbSuptermeq()       { return "⊵"; }

  public String symbSqSupset()        { return "⊐"; }
  public String symbSqSupseteq()      { return "⊒"; }
  public String symbSucc()            { return "≻"; }
  public String symbSucceq()          { return "≽"; }
  public String symbGreater()         { return ">"; }
  public String symbSmaller()         { return "<"; }
  public String symbGeq()             { return "≥"; }
  public String symbLeq()             { return "≤"; }
  public String symbLangle()          { return "⟨"; }
  public String symbRangle()          { return "⟩"; }
  public String symbDistinct()        { return "≠"; }
  public String symbApprox()          { return "≈"; }

  public String symbSharp()           { return "♯"; }
  public String symbBullet()          { return "•"; }
  public String symbStar()            { return "☆"; }

  public String symbAlpha()           { return "α"; }
  public String symbBeta()            { return "β"; }
  public String symbGamma()           { return "γ"; }
  public String symbDelta()           { return "δ"; }
  public String symbEpsilon()         { return "ε"; }
  public String symbZeta()            { return "ζ"; }
  public String symbEta()             { return "η"; }
  public String symbTheta()           { return "θ"; }
  public String symbIota()            { return "ι"; }
  public String symbKappa()           { return "κ"; }
  public String symbLambda()          { return "λ"; }
  public String symbMu()              { return "μ"; }
  public String symbNu()              { return "ν"; }
  public String symbXi()              { return "ξ"; }
  public String symbPi()              { return "π"; }
  public String symbRho()             { return "ρ"; }
  public String symbSigma()           { return "σ"; }
  public String symbTau()             { return "τ"; }
  public String symbPhi()             { return "φ"; }
  public String symbChi()             { return "χ"; }
  public String symbPsi()             { return "ψ"; }
  public String symbOmega()           { return "ω"; }
}

