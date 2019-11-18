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
import cora.exceptions.NullInitialisationError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;

/**
 * BinderVariable is a variable in Vfree, which is allowed to be used as a binder, but does not
 * freely occur in rules.  BinderVariables *can* freely occur in terms, however.
 */
public class BinderVariable extends VariableInherit implements Variable {
  /** Create a binder variable with the given name and type. */
  public BinderVariable(String name, Type type) {
    super(name, type);
    if (name == null) throw new NullInitialisationError("BinderVariable", "name");
  }

  /** 
   * Create a binder variable without a name.
   * This will still give a consistent representation when debug printing a term (using toString()),
   * but gives Cora significant freedom in choosing a suitable name when pretty printing.
   */
  public BinderVariable(Type type) {
    super(null, type);
  }

  /** @return true */
  public boolean isBinderVariable() {
    return true;
  }

  /** @return false, since binder variables may not be used in first-order term rewriting */
  public boolean isFirstOrder() {
    return false;
  }

  /** 
   * For matching, we say that a binder variable ONLY matches another binder variable.  That is, the
   * match function returns the substitution that maps free variables to arbitrary terms and binder
   * variables to binder variables, such that <this> <gamma> = <other>.
   *
   * If this works, then null is returned.
   * If the other term is not a binder variable, then an explanation of the match failure is
   * returned.  The same happens if x is already mapped to a different variable.
   * If x is already mapped to the given other variable, then nothing is done but null is returned.
   * If other or gamma is null, then a NullCallError is thrown instead.
   */
  public String match(Term other, Substitution gamma) {
    if (other == null) throw new NullCallError("BinderVariable", "match", "other (matched term)");
    if (gamma == null) {
      throw new NullCallError("BinderVariable", "match", "gamma (matching substitution");
    }

    if (!other.isVariable() || (!((Variable)other).isBinderVariable())) {
      return "Binder variable " + toString() + " cannot be mapped to " + other.toString() + ".";
    }

    Term previous = gamma.get(this);
    
    if (previous == null) {
      gamma.extend(this, other);
      return null;
    }   
    else if (previous.equals(other)) return null;
    else return "Binder Variable " + toString() + " mapped both to " + previous.toString() +
      " and to " + other.toString() + ".";
  }
}

