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

package cora.terms;

import cora.exceptions.NullCallError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;

/**
 * Var is the default kind of Variable: a free variable that may have any type.
 * Such variables can both be used as parts of constraints and as generic expressions in terms and
 * open spots for matching in rules; however, they cannot be used as binders in an abstraction.
 */
public class Var extends VariableInherit implements Variable {
  /** Create a variable with the given name and type. */
  public Var(String name, Type type) {
    super(name, type);
  }

  /** Create a variable without a name; a name will be automatically generated. */
  public Var(Type type) {
    super("x[" + COUNTER + "]", type);
  }

  /** @return false, since a free variable may not be used as a binder */
  public boolean isBinderVariable() {
    return false;
  }

  /** 
   * This method updates gamma by adding the extension from x to the given other term, if x is not
   * yet mapped to anything.
   * If this works, then null is returned.
   * If x is already mapped to the given other term, then nothing is done but null is returned.
   * If x is mapped to a different term, then an explanation of the match failure is returned.
   * If other or gamma is null, then a NullCallError is thrown instead.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("Var", "match", "other (matched term)");
    if (gamma == null) throw new NullCallError("Var", "match", "gamma (matching substitution");

    Term previous = gamma.get(this);
    
    if (previous == null) {
      gamma.extend(this, other);
      return null;
    }   
    else if (previous.equals(other)) return null;
    else return "Variable " + queryName() + " mapped both to " + previous.toString() + " and to " +
      other.toString() + ".";
  }
}

