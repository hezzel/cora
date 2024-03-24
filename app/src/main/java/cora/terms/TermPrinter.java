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

package cora.terms;

import java.util.Arrays;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import java.util.function.Predicate;
import charlie.exceptions.UnexpectedPatternError;
import charlie.exceptions.IllegalArgumentError;
import charlie.types.TypePrinter;

/**
 * TermPrinters are used in the overall output process of the tool.  This class provides a default
 * implementation, but is meant to be inherited.  You can for instance instantiate the term printer
 * to use unicode symbols, ascii-art, html, print smt-style or whatever is needed.
 */
public class TermPrinter {
  private TypePrinter _typePrinter;       // the printer for types (in abstractions)
  private TreeSet<String> _blockedNames;  // the names that may not be used as variable names

  /** A Renaming is used to assign a new name to (meta-)variables in a term. */
  public final class Renaming {
    private TreeMap<Replaceable,String> _map;
    private TreeSet<String> _avoid;
    public Renaming() {
      _map = new TreeMap<Replaceable,String>();
      _avoid = new TreeSet<String>(_blockedNames);
    }
    /** Returns the chosen name for the given replaceable, or null if it's not in the domain. */
    public String get(Replaceable x) { return _map.get(x); }
    /**
     * Returns whether the given name is available to be used for further renamings.
     * (The renaming is set up so that any name that is already in use is not available, along
     * with the "avoid" names given in the TermPrinter's constructor, and potentially some other
     * names).
     */
    public boolean isAvailable(String name) { return !_avoid.contains(name); }
  }

  /**
   * Generates a TermPrinter.
   * @param avoid names in this set will not be used as generated variable names in the default
   *   functionality (this is intended to be used for instance by the symbols in the alphabet)
   */
  public TermPrinter(TypePrinter types, Set<String> avoid) {
    _blockedNames = new TreeSet<String>(avoid);
    _typePrinter = types;
  }

  /**
   * This access function to generateUniqueNaming can be called with an arbitrary number of
   * term arguments.
   */
  public final Renaming generateUniqueNaming(Term ...terms) {
    return generateUniqueNaming(Arrays.asList(terms));
  }

  /**
   * When printing a term, both free and bound variables (as well as meta-variables) may be renamed
   * in the string output.  This is because variables are not defined by their name, and therefore
   * two distinct variables may have the same name, which could be very confusing (yet, printing
   * variables by their index is generally not pleasant for human readers).
   *
   * This function generates a naming for all the free variables and meta-variables in the given
   * set of terms.  Bound variables are not included, and should be handled in printAbstraction.
   *
   * Note that it is necessary to use generateUniqueNaming if you want to print multiple terms that
   * may have some of the same variables, and you want the same variables to be printed with the
   * same name in all of them: then you should generate a renaming that takes all these terms into
   * account, and use this as an argument to the print function.
   *
   * To influence the chosen names, override the generateNames function.
   */
  public final Renaming generateUniqueNaming(List<Term> terms) {
    TreeMap<String,TreeSet<Replaceable>> existingNames = new TreeMap<String,TreeSet<Replaceable>>();
    // group (meta-)variables by name, so we can see how often each name occurs
    for (Term t : terms) {
      for (Replaceable x : t.freeReplaceables()) {
        String name = x.queryName();
        if (!existingNames.containsKey(name)) {
          TreeSet<Replaceable> tmp = new TreeSet<Replaceable>();
          tmp.add(x);
          existingNames.put(name, tmp);
        }
        else existingNames.get(name).add(x);
      }
    }
    // to generate a new renaming that assigns them all distinct names, we first assign names for
    // the replaceables whose name is already unique (since they can likely be unchanged), and then
    // for the rest
    Renaming ret = new Renaming();
    for (int i = 0; i < 2; i++) {
      for (TreeSet<Replaceable> set : existingNames.values()) {
        if (i == 0 && set.size() != 1) continue;
        if (i == 1 && set.size() == 1) continue;
        int counter = 0;
        for (Replaceable x : set) {
          counter++;
          String name = generateName(x, n -> ret.isAvailable(n), counter, set.size());
          ret._map.put(x, name);
          ret._avoid.add(name);
          if (!name.equals(x.queryName())) ret._avoid.add(x.queryName());
        }
      }
    }
    return ret;
  }

  /**
   * This function generates a name to be used for a free variable or meta-variable.  This might be
   * its own name, a name that uses this name as a base, or something else entirely.
   *
   * @param available returns true if the given name is still unused (and not blocked)
   * @param count,num: there are <num> free variables or meta-variables that have the same name as
   *   the base, and in order of creation, this one has index <count> of them (so 1 ≤ count ≤ num)
   *
   * The default behaviour tries to keep names where possible, and if that is a bad choice
   * (especially if the resulting name is not available) then it instead generates a name of the
   * form name__count.
   * Override to create different name choices.
   */
  protected String generateName(Replaceable x, Predicate<String> available, int count, int num) {
    String base = x.queryName();
    if (base.equals("")) base = "VAR";
    else if (!isGoodNameStart(base.charAt(0))) base = "_" + base;
    if (num == 1 && available.test(base)) return base;
    String name = base + "__" + count;
    if (available.test(name)) return name;
    count = num;
    do {
      count++;
      name = base + "__" + count;
    } while (!available.test(name));
    return name;
  }

  /**
   * Helper function for the default implementation of generateName: returns true if it is likely
   * to be confusing to use a variable name starting with the given letter, and false otherwise.
   * This is quite arbitrary, so this is private functionality; if someone wants to override
   * generateName, they can implement their own preferences!
   */
  private boolean isGoodNameStart(char c) {
    if (c == '#' || c == '$' || c == '?') return true;
    return c >= 'A' && c != '[' && c != ']';
  }

  /**
   * This updates the given renaming to set the name for the given replaceable to name.  It also
   * marks the given name as unavailable for future assignments.
   *
   * Note: if the given name is not available, then an IllegalArgumentError is thrown.
   */
  protected final void assignName(Renaming naming, Replaceable x, String name) {
    if (naming._avoid.contains(name)) {
      throw new IllegalArgumentError("TermPrinter", "assignName",
                                     "choosing unavailable name " + name);
    }
    naming._map.put(x, name);
    naming._avoid.add(name);
  }

  /**
   * This updates the given renaming to remove the name for the given replaceable, and marks the
   * replaceable as available.
   */
  protected final void unassignName(Renaming naming, Replaceable x) {
    String name = naming._map.get(x);
    naming._map.remove(x);
    if (name != null) naming._avoid.remove(name);
  }

  /**
   * Returns a string representation of the given term (using the print function that takes two
   * arguments).
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final String print(Term term) {
    StringBuilder builder = new StringBuilder();
    print(term, builder);
    return builder.toString();
  }

  /**
   * Returns a string representation of the given term using the given Renaming (and using the
   * print function that takes two arguments).
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final String print(Term term, Renaming naming) {
    StringBuilder builder = new StringBuilder();
    print(term, naming, builder);
    return builder.toString();
  }

  /**
   * Adds a string representation of the given term to the given string builder (using the print
   * function that takes two arguments).
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final void print(Term term, StringBuilder builder) {
    print(term, generateUniqueNaming(term), builder);
  }

  /**
   * Adds a string representation of the given term to the given string builder, using the given
   * Renaming to print names for variables.  Note that the renaming should have been created
   * specifically for this term (perhaps among others); if this is not the case, it is possible that
   * some distinct variables will be printed with the same name.
   *
   * To define a custom TermPrinter, you can either override this method directly -- in which case
   * there is no need to override any of the other methods in the class except perhaps
   * generateName if you also wish to override the default variable name generation -- or directly
   * override (some of) the functions it calls: these are the functions print<Something>.
   */
  public void print(Term term, Renaming naming, StringBuilder builder) {
    if (term.isVariable()) printVariable(term.queryVariable(), naming, builder);
    else if (term.isVarTerm()) printVarTerm(term, naming, builder);
    else if (term.isValue()) printValue(term.toValue(), builder);
    else if (term.isConstant()) {
      FunctionSymbol root = term.queryRoot();
      if (root.isTheorySymbol()) printSoloCalculationSymbol(root.toCalculationSymbol(), builder);
      else printConstant(root, builder);
    }
    else if (term.isFunctionalTerm()) {
      FunctionSymbol root = term.queryRoot();
      if (!root.isTheorySymbol()) printFunctionalTerm(term, naming, builder);
      else if (term.queryType().isArrowType()) printPartialTheoryTerm(term, naming, builder);
      else printFullTheoryTerm(term, naming, builder);
    }
    else if (term.isTuple()) printTuple(term, naming, builder);
    else if (term.isAbstraction()) printAbstraction(term, naming, builder);
    else if (term.isMetaApplication()) printMetaApplication(term, naming, builder);
    else if (term.isApplication()) printApplication(term, naming, builder);
    else throw new UnexpectedPatternError("TermPrinter", "print", "one of the standard term shapes",
      "something else");
  }

  /**
   * Called by print() to print a (binder or free) variable.
   *
   * When using the default implementations of printVarTerm and printApplication, it is also called
   * to print the head x of a var term x(s1,...,sn).
   * (If you only want to use this function to print stand-alone variables, then override the
   * default implementation of printVarTerm.)
   *
   * The default implementation uses the renaming, and if no renaming for this variable is defined
   * then it uses the variable's base name.
   */
  protected void printVariable(Variable variable, Renaming naming, StringBuilder builder) {
    String name = naming._map.get(variable);
    if (name == null) builder.append(variable.queryName());
    else builder.append(name);
  }

  /**
   * Called by print() to print a non-theory function symbol.
   *
   * When using the default implementations of printFunctionalTerm and printApplication, it is also
   * called to print the root symbol f of a functional term f(s1,...,sn).
   * (If you only want to use this function to print stand-alone constants, then override the
   * default implementation of printFunctionalTerm.)
   *
   * Note that theory function symbols are printed through either printValue or
   * printSoloCalculationSymbol.
   *
   * The default functionality just prints the constant's name.
   */
  protected void printConstant(FunctionSymbol constant, StringBuilder builder) {
    builder.append(constant.queryName());
  }

  /**
   * Called by print() to print a (theory) value.
   *
   * The default functionality just prints the value's name.
   */
  protected void printValue(Value value, StringBuilder builder) {
    builder.append(value.queryName());
  }

  /**
   * Called by print() to print a calculation symbol (that is used stand-alone).
   *
   * When using the default implementations of printPartialTheoryTerm and printApplication, it is
   * also called to print the root symbol f of a functional term f(s1,...,sn) if (a) that root
   * symbol is a calculation symbol, and (b) the term is not fully applied (so: has higher type).
   * (If you only want to use this function to print stand-alone calculation symbols, then override
   * the default implementation of printPartialTheoryTerm.)
   *
   * The default functionality prints [name], where name is the name of the constant.
   */
  protected void printSoloCalculationSymbol(CalculationSymbol constant, StringBuilder builder) {
    builder.append("[");
    builder.append(queryCalculationName(constant.queryKind(), constant.queryName()));
    builder.append("]");
  }

  /**
   * Called by print() to print a var-term that is not a variable: an application whose head is a
   * variable, and which takes at least 1 argument.
   *
   * The default implementation just calls printApplication.
   */
  protected void printVarTerm(Term term, Renaming naming, StringBuilder builder) {
    printApplication(term, naming, builder);
  }
  
  /**
   * Called by print() to print a standard functional term: an application whose head is a
   * non-theory function symbol, and which takes at least 1 argument.
   *
   * The default functionality just calls printApplication.
   *
   * Note that functional terms whose root symbol is a theory symbol are printed either through
   * printPartialTheoryTerm or printFullTheoryTerm, and that if n = 0, printConstant is called
   * directly instead.
   */
  protected void printFunctionalTerm(Term term, Renaming naming, StringBuilder builder) {
    printApplication(term, naming, builder);
  }

  /**
   * Called by print() to print a functional term of the form f(s1,...,sn) where (a) f is a
   * calculation symbol, and (b) the term is of higher type, so not maximally applied.
   *
   * The default functionality just calls printApplication.
   *
   * Note that functional terms that are fully applied are printed through printFullTheoryTerm.
   */
  protected void printPartialTheoryTerm(Term term, Renaming naming, StringBuilder builder) {
    printApplication(term, naming, builder);
  }

  /**
   * Called by print() to print a base-type functional term f(s1,...,sn) whose root symbol is a
   * calculation symbol (which also implies that n ≥ 1).
   *
   * The default functionality calls either printUnaryCalculation() or printInfix(), depending on
   * whether there are one or two arguments. (There are currently no calculation symbols in Cora
   * that take more than two arguments, but if one such occurs, printApplication is called instead.)
   *
   * Note that functional terms with a calculation symbol as root but which are not fully applied
   * are printed through printPartialTheoryTerm or (if they have no arguments) through
   * printSoloCalculationSymbol.  Values are printed through printValue.
   */
  protected void printFullTheoryTerm(Term term, Renaming naming, StringBuilder builder) {
    CalculationSymbol root = term.queryRoot().toCalculationSymbol();

    if (term.numberArguments() == 0) {  // this shouldn't really happen, but just in case
      printSoloCalculationSymbol(root, builder);
    }
    else if (term.numberArguments() == 1) {  // this happens for NOT and MINUS
      printUnaryCalculation(root, term.queryArgument(1), naming, builder);
    }
    else if (term.numberArguments() == 2 &&
             root.queryAssociativity() != CalculationSymbol.Associativity.NOT_INFIX) {
      printInfix(root, term.queryArgument(1), term.queryArgument(2), naming, builder);
    }
    else { // this shouldn't really happen, but just in case
      printApplication(term, naming, builder);
    }
  }

  /**
   * Called by the default implementation of printFullTheoryTerm() for printing a base-type term
   * f(s), where f is a calculation symbol.
   *
   * The default implementation prints either fs or f(s), depending on the shape of s.  Note that
   * this assumes that functional terms are typically printed in a form g(a1,...,an) and therefore
   * do not need brackets; override (or override printFullTheoryTerm or printTerm) if this is not
   * the case.
   */
  protected void printUnaryCalculation(CalculationSymbol rootsymb, Term arg, Renaming naming,
                                       StringBuilder builder) {
    boolean brackets = arg.isFunctionalTerm() && arg.queryRoot().toCalculationSymbol() != null;
    if (!brackets && arg.isValue()) {
      Value v = arg.toValue();
      if (v.isIntegerValue() && v.getInt() < 0) brackets = true;
    }
    builder.append(queryCalculationName(rootsymb.queryKind(), rootsymb.queryName()));
    if (brackets) builder.append("(");
    print(arg, naming, builder);
    if (brackets) builder.append(")");
  }

  /**
   * Called by the default implementation of printFullTheoryTerm() for printing a base-type term
   * f(left, right) where f is a calculation system that may be printed in infix notation.
   *
   * The default functionality determines whether left and right should have brackets based on the
   * root symbol of left/right (if any) and the associativity of f, and then prints:
   * <maybeleftopen>left<maybeleftclose><operator><mayberightopen>right<mayberightclose>
   * where <operator> is printed using printInfixOperator.
   *
   * Moreover, if root is the PLUS symbol, and right is negative (so either a negative constant or
   * a term with root symbol MINUS), then right is negated and the operator printed as MINUS
   * instead.
   *
   * Note that if you mostly like this default functionality and only want to change the way the
   * operator is printed, it suffices to override printInfixOperator.  However, this default
   * implementation ONLY prints brackets surrounding terms whose root symbol is a calculation
   * symbol; if this is undesirable, you should override the whole function instead.
   */
  protected void printInfix(CalculationSymbol root, Term left, Term right, Renaming naming,
                            StringBuilder builder) {
    CalculationSymbol.Kind rootkind = root.queryKind();
    String rootname = root.queryName();

    // special case: replacing + by -
    if (root.queryKind().equals(CalculationSymbol.Kind.PLUS)) {
      if (right.isFunctionalTerm() && right.queryRoot().toCalculationSymbol() != null &&
          right.queryRoot().toCalculationSymbol().queryKind().equals(CalculationSymbol.Kind.MINUS)) {
        rootkind = CalculationSymbol.Kind.MINUS;
        rootname = "-";
        right = right.queryArgument(1);
      }
      else if (right.isValue() && right.toValue().getInt() < 0) {
        rootkind = CalculationSymbol.Kind.MINUS;
        rootname = "-";
        right = new IntegerValue(-right.toValue().getInt());
      }
    }

    int leftpriority = root.queryInfixPriority();
    int rightpriority = root.queryInfixPriority();
    if (root.queryAssociativity().equals(CalculationSymbol.Associativity.ASSOC_LEFT) &&
        left.isFunctionalTerm() && left.queryRoot().equals(root)) leftpriority--;
    if (root.queryAssociativity().equals(CalculationSymbol.Associativity.ASSOC_RIGHT) &&
        right.isFunctionalTerm() && right.queryRoot().equals(root)) rightpriority--;
    printInfixHelper(left, naming, builder, leftpriority);
    printInfixOperator(rootkind, rootname, builder);
    printInfixHelper(right, naming, builder, rightpriority);
  }

  /**
   * Called by the default functionality for printInfix to print the given operator.
   * Note that the operator may be any infix operator, but also MINUS (which is here used in a
   * binary way).
   */
  protected void printInfixOperator(CalculationSymbol.Kind operatorkind, String operatorname,
                                    StringBuilder builder) {
    builder.append(" ");
    builder.append(queryCalculationName(operatorkind, operatorname));
    builder.append(" ");
  }

  /**
   * This function prints the given argument to the string builder, putting it in brackets if it's
   * a term with infix root of priority ≤ priority.
   */
  private void printInfixHelper(Term arg, Renaming naming, StringBuilder builder, int priority) {
    boolean brackets = false;
    if (arg.isFunctionalTerm()) {
      CalculationSymbol root = arg.queryRoot().toCalculationSymbol();
      if (root != null && root.queryInfixPriority() > 0) {
        brackets = root.queryInfixPriority() <= priority;
      }
    }
    if (brackets) builder.append("(");
    print(arg, naming, builder);
    if (brackets) builder.append(")");
  }

  /**
   * Called by print() to print a tuple.
   *
   * The default functionality prints a shape ⦇s1,...,sn⦈ -- however, to print the opening and
   * closing bracket, queryTupleOpenBracket() and queryTupleCloseBracket() are called.  To keep the
   * default functionality but different brackets, override those two functions instead.
   */
  protected void printTuple(Term term, Renaming naming, StringBuilder builder) {
    builder.append(queryTupleOpenBracket());
    for (int i = 1; i <= term.numberTupleArguments(); i++){
      if (i > 1) builder.append(", ");
      print(term.queryTupleArgument(i), naming, builder);
    }   
    builder.append(queryTupleCloseBracket());
  }

  /**
   * Called by print() to print an abstraction.
   *
   * The default functionality prints LAMBDA <varname>.subterm, where LAMBDA is the symbol given by
   * queryLambda().  To print the varname, the "available" function in the renaming is checked:
   *
   * - if the variable's base name is still available, it becomes the varname
   * - otherwise, the first <base_name>i with i ≥ 1 that is still available becomes the varname
   *
   * This name is added to naming in order to print the subterm, but removed again before the
   * function returns.
   *
   * Note: if a name already exists for the binder, this name is ignored (and restored at the end
   * of the function).  Hence, there is no point in assigning names to bound variables at the start
   * of the printing process.
   */
  protected void printAbstraction(Term term, Renaming naming, StringBuilder builder) {
    Variable binder = term.queryVariable();
    String backup = naming._map.get(binder);

    // find varname
    String bname = binder.queryName();
    String name = bname;
    for (int i = 1; naming._avoid.contains(name); i++) name = bname + i;
    naming._map.put(binder, name);
    naming._avoid.add(name);

    // print term
    builder.append(queryLambda());
    builder.append(name);
    builder.append(".");
    print(term.queryAbstractionSubterm(), naming, builder);

    // restore naming
    if (backup == null) naming._map.remove(binder);
    else naming._map.put(binder, backup);
    naming._avoid.remove(name);
  }

  /**
   * Called by print() to print a meta-application with at least one argument.
   *
   * The default functionality prints <metaname><metaopen>arg1, ..., argn<metaclose>, where
   * - <metaname> is given by the renaming; if the meta-variable does not occur in the naming then
   *   its base name is used instead
   * - <metaopen> is given by queryMetaOpenBracket()
   * - <metaclose> is given by queryMetaCloseBracket()
   */
  protected void printMetaApplication(Term term, Renaming naming, StringBuilder builder) {
    MetaVariable mvar = term.queryMetaVariable();
    String name = naming.get(mvar);
    if (name == null) builder.append(mvar.queryName());
    else builder.append(name);
    builder.append(queryMetaOpenBracket());
    for (int i = 1; i <= term.numberMetaArguments(); i++) {
      if (i != 1) builder.append(", ");
      print(term.queryMetaArgument(i), naming, builder);
    }
    builder.append(queryMetaCloseBracket());
  }

  /**
   * Called by print() to print an application where the head is not a function symbol or variable,
   * and called by the default implementation of printVarTerm, printFunctionalTerm and
   * printPartialTheoryTerm to print an application where the head is a function symbol or variable
   * (with the exception of base-type applications with the head a calculation symbol, which are
   * handled through the default implementation of printFullTheoryTerm).
   *
   * The default functionality prints head(arg1,...,argn), or (head)(arg1,...,argn) if head is an
   * abstraction.
   */
  protected void printApplication(Term term, Renaming naming, StringBuilder builder) {
    Term head = term.queryHead();
    if (head.isAbstraction()) builder.append("(");
    print(head, naming, builder);
    if (head.isAbstraction()) builder.append(")");
    builder.append("(");
    for (int i = 1; i <= term.numberArguments(); i++) {
      if (i > 1) builder.append(", ");
      print(term.queryArgument(i), naming, builder);
    }
    builder.append(")");
  }

  /**
   * If the default printTuple() functionality is used, then you can override this to change the
   * bracket that is used to open a tuple.
   */
  protected String queryTupleOpenBracket() { return "⦇"; }
  /**
   * If the default printTuple() functionality is used, then you can override this to change the
   * bracket that is used to close a tuple.
   */
  protected String queryTupleCloseBracket() { return "⦈"; }
  /**
   * If the default printAbstraction() functionality is used, then you can override this to change
   * the lambda abstraction symbol.
   */
  protected String queryLambda() { return "λ"; }
  /**
   * If the default printMetaApplication() functionality is used, then you can override this to
   * change the opening bracket for a meta-application.
   */
  protected String queryMetaOpenBracket() { return "⟨"; }
  /**
   * If the default printMetaApplication() functionality is used, then you can override this to
   * change the closing bracket for a meta-application.
   */
  protected String queryMetaCloseBracket() { return "⟩"; }
  /**
   * If the default names of the in-built calculation symbols do not suit you, then you can override
   * this to return a different name.
   */
  protected String queryCalculationName(CalculationSymbol.Kind kind, String defaultName) {
    return defaultName;
  }
}

