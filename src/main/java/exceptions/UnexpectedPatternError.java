/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.exceptions;

/**
 * Some interfaces define a kind of object which can have various patterns (eg, a Type is either
 * ARROW(σ,τ) with σ,τ types, or BASE(c, [σ1,...,σn]) with c a type constructor and all σi types.
 * There are some features that exclusively enumerate all possible patterns.  If a pattern is
 * given that is not enumerated -- typically because a new pattern was introduced later -- an
 * UnexpectedPatternError is thrown.
 */
public class UnexpectedPatternError extends Error {
  public UnexpectedPatternError(String classname, String functionname, String expected,
                                String given) {
    super("Unexpected pattern encountered: calling " + classname + "::" + functionname + " with " +
      given + " while " + expected + " was expected.");
  }
}

