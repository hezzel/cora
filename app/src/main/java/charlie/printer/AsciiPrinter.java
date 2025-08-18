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

/** The AsciiPrinter prints with only standard characters */
public class AsciiPrinter extends Printer {
  public AsciiPrinter(TypePrinter ty, PositionPrinter po, TermPrinter te) {
    super(ty, te, po);
  }

  public String symbRuleArrow()       { return "->"; }
  public String symbTypeArrow()       { return "->"; }
  public String symbMapsto()          { return "|->"; }
  public String symbThickArrow()      { return "=>"; }
  public String symbLongArrow()       { return "-->"; }
  public String symbDownArrow()       { return "!down"; }
  public String symbRevRuleArrow()    { return "<-"; }

  public String symbVdash()           { return "|-"; }
  public String symbVDash()           { return "|="; }
  public String symbForall()          { return "FORALL "; }
  public String symbExists()          { return "EXISTS "; }
  public String symbAnd()             { return "/\\"; }
  public String symbOr()              { return "\\/"; }
  public String symbNot()             { return "not "; }
  public String symbImplies()         { return "=>"; }
  public String symbIff()             { return "<=>"; }

  public String symbEmptySet()        { return "{}"; }
  public String symbUnion()           { return "UNION"; }
  public String symbSubterm()         { return "|<|"; }
  public String symbSubtermeq()       { return "|<=|"; }
  public String symbSupterm()         { return "|>|"; }
  public String symbSuptermeq()       { return "|>=|"; }

  public String symbSqSupset()        { return "[>]"; }
  public String symbSqSupseteq()      { return "[>=]"; }
  public String symbSucc()            { return "(>)"; }
  public String symbSucceq()          { return "(>=)"; }
  public String symbGreater()         { return ">"; }
  public String symbSmaller()         { return "<"; }
  public String symbGeq()             { return ">="; }
  public String symbLeq()             { return "<="; }
  public String symbLangle()          { return "<"; }
  public String symbRangle()          { return ">"; }
  public String symbDistinct()        { return "!="; }
  public String symbApprox()          { return "[=]"; }

  public String symbSharp()           { return "#"; }
  public String symbBullet()          { return "*"; }
  public String symbStar()            { return "*"; }

  public String symbAlpha()           { return "alpha"; }
  public String symbBeta()            { return "beta"; }
  public String symbGamma()           { return "gamma"; }
  public String symbDelta()           { return "delta"; }
  public String symbEpsilon()         { return "epsilon"; }
  public String symbZeta()            { return "zeta"; }
  public String symbEta()             { return "eta"; }
  public String symbTheta()           { return "theta"; }
  public String symbIota()            { return "iota"; }
  public String symbKappa()           { return "kappa"; }
  public String symbLambda()          { return "\\"; }
  public String symbMu()              { return "mu"; }
  public String symbNu()              { return "nu"; }
  public String symbXi()              { return "xi"; }
  public String symbPi()              { return "pi"; }
  public String symbRho()             { return "rho"; }
  public String symbSigma()           { return "sigma"; }
  public String symbTau()             { return "tau"; }
  public String symbPhi()             { return "phi"; }
  public String symbChi()             { return "chi"; }
  public String symbPsi()             { return "psi"; }
  public String symbOmega()           { return "omega"; }
}

