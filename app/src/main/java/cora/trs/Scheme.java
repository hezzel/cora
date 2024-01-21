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

package cora.trs;

/**
 * Rule schemes are a way to represent a countably infinite set of rules.  Their behaviour is
 * implemented in the rewriting module, since most analysis techniques mostly need to know whether
 * they are present or not.
 */
public sealed interface Scheme {
  public record Beta() implements Scheme {
    public String toString() { return "β : (λx.s)(t_0,...,t_n) → s[x:=t_0](t_1,...,t_n)"; }
  }

  public record Eta() implements Scheme {
    public String toString() { return "η : λx.s x → x if x ∉ FV(s)"; }
  }

  public record Calc() implements Scheme {
    public String toString() {
      return "calc : f(x1,...,xk) → y [f(x1,...,xk) = y] for f ∈ Σ_{theory}";
    }
  }
}

