/**************************************************************************************************
 Copyright 2025--2026 Cynthia Kop

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

import java.util.Arrays;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Set;
import java.util.function.Predicate;
import charlie.types.Type;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;

/**
 * TermPrinters are used in the overall output process of the tool.  This class provides a default
 * implementation, but is meant to be inherited.  You can for instance instantiate the term printer
 * to use unicode symbols, ascii-art, html, print smt-style or whatever is needed.
 */
public class TermPrinter {
  private NameGenerator _nameGenerator;   // used to generate names for free (meta-)variables

  /**
   * Generates a TermPrinter.
   * @param generator Use this generator to generate names for free variables and meta-variables.
   */
  public TermPrinter(NameGenerator generator) {
    _nameGenerator = generator;
  }

  /**
   * This creates a term printer with a default name generator that does not consider the names of
   * any function symbols (and thus, might inadvertently give a variable a name that is already used
   * by a function symbol).  Only meant for use in unit testing and debugging (but also used in the
   * default Term::toString() functionality, which exists for that purpose).
   *
   * In general, if you want to use the default term printing functionality, it is recommended to
   * use the standard constructor and create the NameGenerator using TRS::createNameGenerator().
   */
  public static TermPrinter createDebugTermPrinter() {
    return new TermPrinter(new NameGenerator(Set.of()));
  }

  /** Returns the NameGenerator that we are using to name free variables and meta-variables. */
  public NameGenerator queryNameGenerator() {
    return _nameGenerator;
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
   * print function that takes two arguments).  Note that the renaming is expected to have all
   * free replaceables of the given term in its domain, or the output may be confusing.
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
    print(term, _nameGenerator.generateUniqueNaming(term), builder);
  }

  /**
   * Adds a string representation of the given term to the given string builder, using the given
   * Renaming to print names for variables.  Note that the renaming should have every free
   * (meta-)variable in term in its domain; if this is not the case, it is possible that some
   * distinct variables will be printed with the same name.
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final void print(Term term, Renaming naming, StringBuilder builder) {
    MutableRenaming mren = _nameGenerator.generateUniqueNaming();
    for (Replaceable r : naming.domain()) mren.avoid(r.queryName());
    for (String m : naming.range()) mren.avoid(m);
    printRecursive(term, naming, mren, builder);
  }

  /**
   * The main print function: it adds a string representation of the given term to the given string
   * builder, using the two given renamings to print names for variables.
   *
   * Here, the boundNaming is intended to be used for terms that occurred bound in the original
   * term.  Hence, it should only contain mappings for binder variables, and is used as leading
   * when deciding what name to use for a variable.  If some variable does not occur in boundNaming,
   * then it is looked up in freeNaming (as are all meta-variables).
   *
   * To define a custom TermPrinter, you can either override this method directly -- in which case
   * there is no need to override any of the other methods in the class except perhaps
   * generateName if you also wish to override the default variable name generation -- or directly
   * override (some of) the functions it calls: these are the functions print<Something>.
   */
  protected final void printRecursive(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                      StringBuilder builder) {
    if (term.isVariable()) printVariable(term.queryVariable(), freeNaming, boundNaming, builder);
    else if (term.isVarTerm()) printVarTerm(term, freeNaming, boundNaming, builder);
    else if (term.isValue()) printValue(term.toValue(), builder);
    else if (term.isConstant()) {
      FunctionSymbol root = term.queryRoot();
      if (root.isTheorySymbol()) printSoloCalculationSymbol(root.toCalculationSymbol(), builder);
      else printConstant(root, builder);
    }
    else if (term.isFunctionalTerm()) {
      FunctionSymbol root = term.queryRoot();
      if (!root.isTheorySymbol()) printFunctionalTerm(term, freeNaming, boundNaming, builder);
      else if (term.queryType().isArrowType()) {
        printPartialTheoryTerm(term, freeNaming, boundNaming, builder);
      }
      else printFullTheoryTerm(term, freeNaming, boundNaming, builder);
    }
    else if (term.isAbstraction()) printAbstraction(term, freeNaming, boundNaming, builder);
    else if (term.isMetaApplication()) printMetaApplication(term, freeNaming, boundNaming, builder);
    else if (term.isApplication()) printApplication(term, freeNaming, boundNaming, builder);
    else throw new IllegalArgumentException("TermPrinter::print called with a term that does " +
      "not have any of the standard term shapes!");
  }

  /**
   * Called by printRecursive() to print a (binder or free) variable.
   *
   * When using the default implementations of printVarTerm and printApplication, it is also called
   * to print the head x of a var term x(s1,...,sn).
   * (If you only want to use this function to print stand-alone variables, then override the
   * default implementation of printVarTerm.)
   *
   * The default implementation uses the name for the variable in boundNaming, or if that doesn't
   * exist, the name in freeNaming.  If there is no name set in either Renaming, then it uses the
   * variable's base name.
   */
  protected void printVariable(Variable variable, Renaming freeNaming, MutableRenaming boundNaming,
                               StringBuilder builder) {
    String name = boundNaming.getName(variable);
    if (name == null) name = freeNaming.getName(variable);
    if (name == null) builder.append(variable.queryName());
    else builder.append(name);
  }

  /**
   * This prints the given replaceable to the string builder in the same way it would be done by
   * printVariable or printMetaApplication, but considers only one renaming (so the given
   * replaceable is not expected to occur bound in the original term).
   *
   * The default implementation uses the renaming, and if no renaming for this Replaceable is
   * defined then it uses its base name.
   */
  public void printReplaceable(Replaceable r, Renaming naming, StringBuilder builder) {
    String name = naming.getName(r);
    if (name == null) builder.append(r.queryName());
    else builder.append(name);
  }

  /**
   * Called by printRecursive() to print a non-theory function symbol.
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
   * Called by printRecursive() to print a (theory) value.
   *
   * The default functionality just prints the value's name.
   */
  protected void printValue(Value value, StringBuilder builder) {
    builder.append(value.queryName());
  }

  /**
   * Called by printRecursive() to print a calculation symbol (that is used stand-alone).
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
    builder.append(queryCalculationName(constant.queryKind(), constant.queryName(),
                                        constant.queryType()));
    builder.append("]");
  }

  /**
   * Called by printRecursive() to print a var-term that is not a variable: an application whose
   * head is a variable, and which takes at least 1 argument.
   *
   * The default implementation just calls printApplication.
   */
  protected void printVarTerm(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                              StringBuilder builder) {
    printApplication(term, freeNaming, boundNaming, builder);
  }
  
  /**
   * Called by printRecursive() to print a standard functional term: an application whose head is a
   * non-theory function symbol, and which takes at least 1 argument.
   *
   * The default functionality just calls printApplication.
   *
   * Note that functional terms whose root symbol is a theory symbol are printed either through
   * printPartialTheoryTerm or printFullTheoryTerm, and that if n = 0, printConstant is called
   * directly instead.
   */
  protected void printFunctionalTerm(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                     StringBuilder builder) {
    printApplication(term, freeNaming, boundNaming, builder);
  }

  /**
   * Called by printRecursive() to print a functional term of the form f(s1,...,sn) where (a) f is
   * a calculation symbol, and (b) the term is of higher type, so not maximally applied.
   *
   * The default functionality just calls printApplication.
   *
   * Note that functional terms that are fully applied are printed through printFullTheoryTerm.
   */
  protected void printPartialTheoryTerm(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                        StringBuilder builder) {
    printApplication(term, freeNaming, boundNaming, builder);
  }

  /**
   * Called by printRecursive() to print a base-type functional term f(s1,...,sn) whose root symbol
   * is a calculation symbol (which also implies that n ≥ 1).
   *
   * The default functionality calls either printUnaryCalculation() or printInfix(), depending on
   * whether there are one or two arguments. (There are currently no calculation symbols in Cora
   * that take more than two arguments, but if one such occurs, printApplication is called instead.)
   *
   * Note that functional terms with a calculation symbol as root but which are not fully applied
   * are printed through printPartialTheoryTerm or (if they have no arguments) through
   * printSoloCalculationSymbol.  Values are printed through printValue.
   */
  protected void printFullTheoryTerm(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                     StringBuilder builder) {
    CalculationSymbol root = term.queryRoot().toCalculationSymbol();

    if (term.numberArguments() == 0) {  // this shouldn't really happen, but just in case
      printSoloCalculationSymbol(root, builder);
    }
    else if (term.numberArguments() == 1) {  // this happens for NOT and MINUS
      printUnaryCalculation(root, term.queryArgument(1), freeNaming, boundNaming, builder);
    }
    else if (term.numberArguments() == 2 &&
             root.queryAssociativity() != CalculationSymbol.Associativity.NOT_INFIX) {
      printInfix(root, term.queryArgument(1), term.queryArgument(2), freeNaming, boundNaming,
                 builder);
    }
    else { // this shouldn't really happen, but just in case
      printApplication(term, freeNaming, boundNaming, builder);
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
  protected void printUnaryCalculation(CalculationSymbol rootsymb, Term arg, Renaming freeNaming,
                                       MutableRenaming boundNaming, StringBuilder builder) {
    boolean brackets = arg.isFunctionalTerm() && arg.queryRoot().toCalculationSymbol() != null;
    if (!brackets && arg.isValue()) {
      Value v = arg.toValue();
      if (v.isIntegerValue() && v.getInteger().signum() < 0) brackets = true;
    }
    builder.append(queryCalculationName(rootsymb.queryKind(), rootsymb.queryName(),
                                        rootsymb.queryType()));
    if (brackets) builder.append("(");
    printRecursive(arg, freeNaming, boundNaming, builder);
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
   * Note that if you mostly like this default functionality and only want to change the way the
   * operator is printed, it suffices to override printInfixOperator.  However, this default
   * implementation ONLY prints brackets surrounding terms whose root symbol is a calculation
   * symbol; if this is undesirable, you should override the whole function instead.
   */
  protected void printInfix(CalculationSymbol root, Term left, Term right, Renaming freeNaming,
                            MutableRenaming boundNaming, StringBuilder builder) {
    CalculationSymbol.Kind rootkind = root.queryKind();
    String rootname = root.queryName();

    int leftpriority = root.queryInfixPriority();
    int rightpriority = root.queryInfixPriority();

    if (root.queryAssociativity().equals(CalculationSymbol.Associativity.ASSOC_LEFT) &&
        left.isFunctionalTerm() && left.queryRoot().equals(root)) leftpriority--;
    if (root.queryAssociativity().equals(CalculationSymbol.Associativity.ASSOC_LEFT_INCLUSIVE)) {
        leftpriority--;
    }
    if (root.queryAssociativity().equals(CalculationSymbol.Associativity.ASSOC_RIGHT) &&
        right.isFunctionalTerm() && right.queryRoot().equals(root)) rightpriority--;
    printInfixHelper(left, freeNaming, boundNaming, builder, leftpriority);
    printInfixOperator(rootkind, rootname, root.queryType(), builder);
    printInfixHelper(right, freeNaming, boundNaming, builder, rightpriority);
  }

  /**
   * Called by the default functionality for printInfix to print the given operator.
   * Note that the operator may be any infix operator, but also MINUS (which is here used in a
   * binary way).
   */
  protected void printInfixOperator(CalculationSymbol.Kind operatorkind, String operatorname,
                                    Type operatortype, StringBuilder builder) {
    builder.append(" ");
    builder.append(queryCalculationName(operatorkind, operatorname, operatortype));
    builder.append(" ");
  }

  /**
   * This function prints the given argument to the string builder, putting it in brackets if it's
   * a term with infix root of priority ≤ priority.
   */
  private void printInfixHelper(Term arg, Renaming freeNaming, MutableRenaming boundNaming,
                                StringBuilder builder, int priority) {
    boolean brackets = false;
    if (arg.isFunctionalTerm()) {
      CalculationSymbol root = arg.queryRoot().toCalculationSymbol();
      if (root != null && root.queryInfixPriority() > 0) {
        brackets = root.queryInfixPriority() <= priority;
      }
    }
    if (brackets) builder.append("(");
    printRecursive(arg, freeNaming, boundNaming, builder);
    if (brackets) builder.append(")");
  }

  /**
   * Called by printRecursive() to print an abstraction.
   *
   * The default functionality prints LAMBDA <varname>.subterm, where LAMBDA is the symbol given by
   * queryLambda().  To print the varname, there are three options:
   *
   * - if the variable does not occur in freeNaming or boundNaming yet, we use the underlying
   *   NameGenerator to generate a new name for this bound variable, store it in boundNaming in
   *   order to print the subterm, and then remove it again before the function returns
   *   (in normal calls to print(), this is the only case that will typically occur)
   * - if the variable occurs in freeNaming (but not in boundNaming), then we don't choose a new
   *   name but simply use the existing choice
   *   (due to the well-behavedness property this will typically only happen if someone calls print
   *   with a renaming that has explicitly had mappings for the bound variables added, so we
   *   respect their choice)
   * - if the variable occurs in boundNaming, we also don't choose a new name but instead use the
   *   existing mapping; the binder is also not removed from boundNaming afterwards
   *   (due to the well-behavedness property this actually should never happen, but it might occur
   *   due to shenanigans in inheriting classes)
   */
  protected void printAbstraction(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                  StringBuilder builder) {
    Variable binder = term.queryVariable();
    boolean remove = false;

    String name = boundNaming.getName(binder);
    if (name == null) name = freeNaming.getName(binder);
    if (name == null) {
      name = _nameGenerator.generateBoundName(boundNaming, binder);
      remove = true;
    }

    // print term
    builder.append(queryLambda());
    printAbstractionBinder(binder, name, builder);
    builder.append(".");
    printRecursive(term.queryAbstractionSubterm(), freeNaming, boundNaming, builder);

    // restore naming
    if (remove) boundNaming.unsetName(binder);
  }

  /**
   * Called by printAbstraction() to print the binder variable in an abstraction.
   * The default functionality just prints the chosen name.
   */
  protected void printAbstractionBinder(Variable binder, String chosenName, StringBuilder builder) {
    builder.append(chosenName);
  }

  /**
   * Called by printRecursive() to print a meta-application with at least one argument.
   *
   * The default functionality prints <metaname><metaopen>arg1, ..., argn<metaclose>, where
   * - <metaname> is given by the renaming; if the meta-variable does not occur in the naming then
   *   its base name is used instead
   * - <metaopen> is given by queryMetaOpenBracket()
   * - <metaclose> is given by queryMetaCloseBracket()
   */
  protected void printMetaApplication(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                      StringBuilder builder) {
    MetaVariable mvar = term.queryMetaVariable();
    String name = freeNaming.getName(mvar);
    if (name == null) builder.append(mvar.queryName());
    else builder.append(name);
    builder.append(queryMetaOpenBracket());
    for (int i = 1; i <= term.numberMetaArguments(); i++) {
      if (i != 1) builder.append(", ");
      printRecursive(term.queryMetaArgument(i), freeNaming, boundNaming, builder);
    }
    builder.append(queryMetaCloseBracket());
  }

  /**
   * Called by printRecursive() to print an application where the head is not a function symbol or variable,
   * and called by the default implementation of printVarTerm, printFunctionalTerm and
   * printPartialTheoryTerm to print an application where the head is a function symbol or variable
   * (with the exception of base-type applications with the head a calculation symbol, which are
   * handled through the default implementation of printFullTheoryTerm).
   *
   * The default functionality prints head(arg1,...,argn), or (head)(arg1,...,argn) if head is an
   * abstraction.
   */
  protected void printApplication(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                  StringBuilder builder) {
    Term head = term.queryHead();
    if (head.isAbstraction()) builder.append("(");
    printRecursive(head, freeNaming, boundNaming, builder);
    if (head.isAbstraction()) builder.append(")");
    builder.append("(");
    for (int i = 1; i <= term.numberArguments(); i++) {
      if (i > 1) builder.append(", ");
      printRecursive(term.queryArgument(i), freeNaming, boundNaming, builder);
    }
    builder.append(")");
  }

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
  protected String queryCalculationName(CalculationSymbol.Kind kind, String defaultName,
                                        Type operatorType) {
    return defaultName;
  }
}

