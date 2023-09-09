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

import java.util.List;
import java.util.ArrayList;
import cora.exceptions.ArityError;
import cora.exceptions.IllegalArgumentError;
import cora.exceptions.IncorrectStringException;
import cora.types.Type;
import cora.types.TypeFactory;

public class TermFactory {
  /** Create a non-binder variable with the given name and type. */
  public static Variable createVar(String name, Type type) {
    return new Var(name, type);
  }

  /**
   * Create a non-binder variable with the given name and the unit sort, for use in unsorted
   * rewriting.
   */
  public static Variable createVar(String name) {
    return new Var(name, TypeFactory.unitSort);
  }

  /** Create a non-binder variable without a name; a name will be automatically generated. */
  public static Variable createVar(Type type) {
    return new Var(type);
  }

  /** Create a variable with auto-generated name and the unit sort, for unsorted rewriting. */
  public static Variable createVar() {
    return new Var(TypeFactory.unitSort);
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
    Type type = TypeFactory.unitSort;
    for (int i = 0; i < arity; i++) type = TypeFactory.createArrow(TypeFactory.unitSort, type);
    return new Constant(name, type);
  }

  /** Creates an Integer Value */
  public static Value createValue(int n) {
    return new IntegerValue(n);
  }

  /** Creates a Boolean Value */
  public static Value createValue(boolean b) {
    return new BooleanValue(b);
  }

  /** Create a String Value */
  public static Value createValue(String s) {
    return new StringValue(s);
  }

  /** Create a String Value with a string in quotes, and potentially with escape characters in it */
  public static Value createEscapedStringValue(String s) throws IncorrectStringException {
    return StringValue.parseUserStringValue(s);
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
    ArrayList<Type> inputs = new ArrayList<Type>();
    for (int i = 0; i < arity; i++) {
      if (!type.isArrowType()) throw new ArityError("TermFactory", "createMetaVar",
        "trying to create a meta-variable with arity " + arity + " while the given type (" +
        type.toString() + ") only has arity " + i);
      inputs.add(type.queryArrowInputType());
      type = type.queryArrowOutputType();
    }
    return new HigherMetaVar(name, inputs, type);
  }

  /** Creates a meta-variable X with arity k */
  public static MetaVariable createMetaVar(String name, ArrayList<Type> inputs, Type output) {
    if (inputs.size() == 0) return new Var(name, output);
    return new HigherMetaVar(name, inputs, output);
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
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(arg1);
    args.add(arg2);
    return head.apply(args);
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

  /** Create a meta-application Z[arg1] */
  public static Term createMeta(MetaVariable mv, Term arg1) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(arg1);
    return new MetaApplication(mv, args);
  }

  /** Create a meta-application Z[arg2] */
  public static Term createMeta(MetaVariable mv, Term arg1, Term arg2) {
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(arg1);
    args.add(arg2);
    return new MetaApplication(mv, args);
  }

  /** Creates an empty substitution. */
  public static Substitution createEmptySubstitution() {
    return new Subst();
  }

  /** Creates the binary calculation symbol for addition. */
  public static CalculationSymbol createPlus() {
    return new PlusSymbol();
  }

  /** Creates the binary calculation symbol for multiplication. */
  public static CalculationSymbol createTimes() {
    return new TimesSymbol();
  }
  
  /** Creates the unary minus symbol for negating an integer. */
  public static CalculationSymbol createMinus() {
    return new MinusSymbol();
  }

  /** Creates the binary calculation symbol for conjunction. */
  public static CalculationSymbol createAnd() {
    return new AndOrSymbol(false);
  }

  /** Creates the binary calculation symbol for disjunction. */
  public static CalculationSymbol createOr() {
    return new AndOrSymbol(true);
  }

  /** Creates the unary calculation symbol for boolean negation. */
  public static CalculationSymbol createNot() {
    return new NotSymbol();
  }

  /** Creates the binary calculation symbol for greater. */
  public static CalculationSymbol createGreater() {
    return new ComparisonSymbol(ComparisonSymbol.KIND_GRE);
  }

  /** Creates the binary calculation symbol for greater. */
  public static CalculationSymbol createSmaller() {
    return new ComparisonSymbol(ComparisonSymbol.KIND_SMA);
  }

  /** Creates the binary calculation symbol for greater. */
  public static CalculationSymbol createGeq() {
    return new ComparisonSymbol(ComparisonSymbol.KIND_GEQ);
  }

  /** Creates the binary calculation symbol for greater. */
  public static CalculationSymbol createLeq() {
    return new ComparisonSymbol(ComparisonSymbol.KIND_LEQ);
  }
}

