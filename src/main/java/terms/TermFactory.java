/**************************************************************************************************
 Copyright 2022 Cynthia Kop

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

import java.util.List;
import cora.types.Type;
import cora.types.TypeFactory;

public class TermFactory {
  /** Create a non-binder variable with the given name and type. */
  public static Variable createVar(String name, Type type) {
    return new Var(name, type, false);
  }

  /**
   * Create a non-binder variable with the given name and the unit sort, for use in unsorted
   * rewriting.
   */
  public static Variable createVar(String name) {
    return new Var(name, TypeFactory.unitSort, false);
  }

  /** Create a non-binder variable without a name; a name will be automatically generated. */
  public static Variable createVar(Type type) {
    return new Var(type, false);
  }

  /** Create a variable with auto-generated name and the unit sort, for unsorted rewriting. */
  public static Variable createVar() {
    return new Var(TypeFactory.unitSort, false);
  }

  /** Create a function symbol with the given name and type. */
  public static FunctionSymbol createConstant(String name, Type type) {
    return new Constant(name, type);
  }

  /** Create an essentially unsorted function symbol with the given name and arity. */
  public static FunctionSymbol createConstant(String name, int arity) {
    Type type = TypeFactory.unitSort;
    for (int i = 0; i < arity; i++) type = TypeFactory.createArrow(TypeFactory.unitSort, type);
    return new Constant(name, type);
  }

  /** Create a varterm or functional term which takes one argument. */
  public static Term createApp(Term head, Term arg) {
    return head.apply(arg);
  }

  /** Create a varterm or functional term which takes two arguments. */
  public static Term createApp(Term head, Term arg1, Term arg2) {
    return head.apply(arg1).apply(arg2);
  }

  /** Create a varterm or functional term with the given arguments. */
  public static Term createApp(Term head, List<Term> args) {
    if (args.size() == 0) return head;
    return head.apply(args);
  }

  /** Creates an empty substitution. */
  public Substitution createEmptySubstitution() {
    return new Subst();
  }
}

