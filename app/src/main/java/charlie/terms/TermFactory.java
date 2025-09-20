/**************************************************************************************************
 Copyright 2022--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.terms;

import java.util.ArrayList;
import java.util.List;
import charlie.util.FixedList;
import charlie.types.*;
import charlie.terms.replaceable.Replaceable;

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
    if (arity < 0) throw new IllegalArgumentException("TermFactory::createMetaVar " +
      "received negative arity " + arity + ".");
    FixedList.Builder<Type> builder = new FixedList.Builder<Type>();
    Type tmp = type;
    for (int i = 0; i < arity; i++) {
      switch (tmp) {
        case Arrow(Type inp, Type out):
          builder.add(inp);
          tmp = out;
          break;
        default: throw new TypingException("Cannot construct meta-variable with type ", type,
          " and arity " + arity + " since the arity may not be larger than the number of input " +
          "arguments to the type.");
      }
    }
    return new HigherMetaVar(name, builder.build(), tmp);
  }

  /** Creates a meta-variable X with arity k */
  public static MetaVariable createMetaVar(String name, FixedList<Type> inputs, Type output) {
    if (inputs.size() == 0) return new Var(name, output);
    return new HigherMetaVar(name, inputs, output);
  }

  /** Creates a meta-variable X with arity k */
  public static MetaVariable createMetaVar(String name, List<Type> inputs, Type output) {
    if (inputs.size() == 0) return new Var(name, output);
    return new HigherMetaVar(name, FixedList.copy(inputs), output);
  }

  /** Creates a meta-variable X with arity 1. */
  public static MetaVariable createMetaVar(String name, Type input, Type output) {
    return new HigherMetaVar(name, FixedList.of(input), output);
  }

  /** Creates a meta-variable X with arity 2. */
  public static MetaVariable createMetaVar(String name, Type in1, Type in2, Type output) {
    return new HigherMetaVar(name, FixedList.of(in1, in2), output);
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
    return head.apply(List.of(arg1, arg2));
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
    return new MetaApplication(mv, List.of(arg));
  }

  /** Create a meta-application Z[arg2] */
  public static Term createMeta(MetaVariable mv, Term arg1, Term arg2) {
    return new MetaApplication(mv, List.of(arg1, arg2));
  }

  /**
   * Creates the meta-application λx1...xn.Z[x1,...,xn] if x is a meta-variable Z,
   * otherwise returns x unmodified.
   */
  public static Term makeTerm(Replaceable x) {
    if (x instanceof Term s) return s;
    if (x instanceof HigherMetaVar z) {
      ArrayList<Term> args = new ArrayList<Term>();
      for (int i = 1; i <= z.queryArity(); i++) {
        args.add(new Binder("b" + i, z.queryInputType(i)));
      }
      Term ret = new MetaApplication(z, args);
      for (int i = args.size()-1; i >= 0; i--) {
        ret = new Abstraction(args.get(i).queryVariable(), ret);
      }
      return ret;
    }
    throw new IllegalArgumentException("Given replaceable " + x.queryName() + " which is " +
      "neither a term nor a higher meta-variable!");
  }
}

