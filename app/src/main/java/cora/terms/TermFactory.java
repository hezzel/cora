/**************************************************************************************************
 Copyright 2022, 2023 Cynthia Kop

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

import com.google.common.collect.ImmutableList;
import java.util.List;
import cora.exceptions.ArityError;
import cora.exceptions.IllegalArgumentError;
import cora.types.Arrow;
import cora.types.Type;
import cora.types.TypeFactory;

public class TermFactory {
  /** Create a non-binder variable with the given name and type. */
  public static Variable createVar(String name, Type type) {
    return new Var(name, type);
  }

  /**
   * Create a non-binder variable with the given name and the default sort, for use in unsorted
   * rewriting.
   */
  public static Variable createVar(String name) {
    return new Var(name, TypeFactory.defaultSort);
  }

  /** Create a non-binder variable without a name; a name will be automatically generated. */
  public static Variable createVar(Type type) {
    return new Var(type);
  }

  /** Create a variable with auto-generated name and the default sort, for unsorted rewriting. */
  public static Variable createVar() {
    return new Var(TypeFactory.defaultSort);
  }

  /** Create a binder variable with the given default name and type. */
  public static Variable createBinder(String name, Type type) {
    return new Binder(name, type);
  }

  /** Create a function symbol with the given name and type. */
  public static FunctionSymbol createConstant(String name, Type type) {
    return new Constant(name, type);
  }

  /** Create an essentially unsorted function symbol with the given name and arity. */
  public static FunctionSymbol createConstant(String name, int arity) {
    Type type = TypeFactory.defaultSort;
    for (int i = 0; i < arity; i++) type = TypeFactory.createArrow(TypeFactory.defaultSort, type);
    return new Constant(name, type);
  }

  /** Creates a functional term f(args) */
  public static Term createFunctionalTerm(FunctionSymbol f, List<Term> args) {
    if (args == null || args.size() == 0) return f;
    return new Application(f, args);
  }

  /** Creates a meta-variable X with arity k */
  public static MetaVariable createMetaVar(String name, Type type, int arity) {
    if (arity == 0) return new Var(name, type);
    if (arity < 0) throw new IllegalArgumentError("TermFactory", "createMetaVar",
      "received negative arity " + arity + ".");
    ImmutableList.Builder<Type> builder = ImmutableList.<Type>builder();
    Type tmp = type;
    for (int i = 0; i < arity; i++) {
      switch (tmp) {
        case Arrow(Type inp, Type out):
          builder.add(inp);
          tmp = out;
          break;
        default: throw new ArityError("TermFactory", "createMetaVar",
          "trying to create a meta-variable with arity " + arity + " while the given type (" +
          type.toString() + ") only has arity " + i);
      }
    }
    return new HigherMetaVar(name, builder.build(), tmp);
  }

  /** Creates a meta-variable X with arity k */
  public static MetaVariable createMetaVar(String name, ImmutableList<Type> inputs, Type output) {
    if (inputs.size() == 0) return new Var(name, output);
    return new HigherMetaVar(name, inputs, output);
  }

  /** Creates a meta-variable X with arity k */
  public static MetaVariable createMetaVar(String name, List<Type> inputs, Type output) {
    if (inputs.size() == 0) return new Var(name, output);
    return new HigherMetaVar(name, ImmutableList.copyOf(inputs), output);
  }

  /** Creates a meta-variable X with arity 1. */
  public static MetaVariable createMetaVar(String name, Type input, Type output) {
    return new HigherMetaVar(name, ImmutableList.<Type>builder().add(input).build(), output);
  }

  /** Creates a meta-variable X with arity 2. */
  public static MetaVariable createMetaVar(String name, Type in1, Type in2, Type output) {
    return new HigherMetaVar(name, ImmutableList.<Type>builder().add(in1).add(in2).build(), output);
  }

  /** Creates a tuple with 2 elements */
  public static Term createTuple(Term a, Term b) {
    return new Tuple(a, b);
  }

  /** Creates a tuple with 3 elements. */
  public static Term createTuple(Term a, Term b, Term c) {
    return new Tuple(a, b, c);
  }

  /** Creates a tuple of arbitrary length ≥ 2. */
  public static Term createTuple(List<Term> elems) {
    return new Tuple(elems);
  }

  /**
   * Create an application which takes one argument.  Here, head may be anything,
   * including another application.
   */
  public static Term createApp(Term head, Term arg) {
    return head.apply(arg);
  }

  /**
   * Create an application which takes two arguments.  Here, head may be anything,
   * including another application.
   */
  public static Term createApp(Term head, Term arg1, Term arg2) {
    return head.apply(ImmutableList.<Term>builder().add(arg1).add(arg2).build());
  }

  /**
   * Create an application with the given head and arguments.  If the head is an application, the
   * given arguments are just appended to the existing argument list.
   */
  public static Term createApp(Term head, List<Term> args) {
    if (args.size() == 0) return head;
    return head.apply(args);
  }

  /** Creates an abstraction λbinder.subterm */
  public static Term createAbstraction(Variable binder, Term subterm) {
    return new Abstraction(binder, subterm);
  }

  /** Creates a meta-application Z[args] */
  public static Term createMeta(MetaVariable mv, List<Term> args) {
    if (args != null && args.size() == 0 && (mv instanceof Var)) return (Var)mv;
    return new MetaApplication(mv, args);
  }

  /** Create a meta-application Z[arg] */
  public static Term createMeta(MetaVariable mv, Term arg) {
    return new MetaApplication(mv, ImmutableList.<Term>builder().add(arg).build());
  }

  /** Create a meta-application Z[arg2] */
  public static Term createMeta(MetaVariable mv, Term arg1, Term arg2) {
    return new MetaApplication(mv, ImmutableList.<Term>builder().add(arg1).add(arg2).build());
  }

  /** Creates an empty substitution. */
  public static Substitution createEmptySubstitution() {
    return new Subst();
  }
}

