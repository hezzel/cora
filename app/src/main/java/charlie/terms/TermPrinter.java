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

import java.util.Set;

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
   * A default term printer that can be used for debugging and unit testing purposes.  This is used
   * by the default toString() functionality in Term, which exists exactly for those two purposes.
   *
   * ### It is not meant to be used for anything else! ###
   *
   * In particular, this uses a default name generator that does not consider the names of any
   * function symbols (and thus, might inadvertently give a variable a name that is already used by
   * a function symbol).  It also does not respect user settings.
   *
   * Note that while the DEBUGPRINTER is not final, the main intention is that you set it at the
   * start of the program (but can do so from a settings / debugging class).
   */
  public static TermPrinter DEBUGPRINTER = new TermPrinter(new NameGenerator(Set.of()));

  /**
   * Generates a TermPrinter.
   * @param generator Use this generator to generate names for free variables and meta-variables.
   */
  public TermPrinter(NameGenerator generator) {
    _nameGenerator = generator;
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
   * builder, using the two given Renamings to print names for variables.
   *
   * Here, the boundNaming is intended to be used for terms that occurred bound in the original
   * term.  Hence, it should only contain mappings for binder variables, and is used as leading
   * when deciding what name to use for a variable.  If some variable does not occur in boundNaming,
   * then it is looked up in freeNaming (as are all meta-variables).
   *
   * To define a custom TermPrinter, you can either override this method directly -- in which case
   * there is no need to override any of the other methods in the class -- or directly override
   * (some of) the functions it calls: these are the functions print<Something>.
   */
  protected final void printRecursive(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                      StringBuilder builder) {
    if (term.isVariable()) printVariable(term.queryVariable(), freeNaming, boundNaming, builder);
    else if (term.isVarTerm()) printVarTerm(term, freeNaming, boundNaming, builder);
    else if (term.isConstant()) {
      FunctionSymbol root = term.queryRoot();
      if (root.isInfixSymbol()) printSoloInfixSymbol(root, builder);
      else printConstant(root, builder);
    }
    else if (term.isFunctionalTerm()) {
      FunctionSymbol root = term.queryRoot();
      if (root.isInfixSymbol() && !term.queryType().isArrowType()) {
        if (term.numberArguments() == 1) {
          printPrefixTerm(term.queryRoot(), term.queryArgument(1),
                          freeNaming, boundNaming, builder);
        }
        else printInfixTerm(term, freeNaming, boundNaming, builder);
      }
      else printFunctionalTerm(term, freeNaming, boundNaming, builder);
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
   * variable's base name, but marks it as undefined using ??.
   */
  protected void printVariable(Variable variable, Renaming freeNaming, MutableRenaming boundNaming,
                               StringBuilder builder) {
    String name = boundNaming.getName(variable);
    if (name == null) name = freeNaming.getName(variable);
    if (name == null) builder.append("??" + variable.queryName());
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
    if (name == null) builder.append("??" + r.queryName());
    else builder.append(name);
  }

  /**
   * Called by printRecursive() to print a standalone, non-infix function symbol.
   *
   * When using the default implementations of printFunctionalTerm and printApplication, it is also
   * called to print the root symbol f of a functional term f(s1,...,sn), so long as f is non-infix.
   *
   * (If you only want to use this function to print stand-alone constants, then override the
   * default implementation of printFunctionalTerm.)
   *
   * The default functionality just prints the constant's name.
   */
  protected void printConstant(FunctionSymbol constant, StringBuilder builder) {
    builder.append(constant.queryName());
  }

  /**
   * Called by printRecursive() to print an infix symbol that is used standalone, and by the
   * default implementations of printFunctionalTerm and printApplication also for an infix symbol
   * that occurs as the root of a *partially applied* functional term [f](s1,...,sn) (with arity(f)
   * ≥ n+1).  Fully applied terms [f](s1,...,sn) with [f] an infix symbol are handled through
   * printInfixTerm.
   *
   * (If you only want to use this function to print stand-alone infix symbols, then override the
   * default implementation of printFunctionalTerm.)
   *
   * The default functionality prints [name].
   */
  protected void printSoloInfixSymbol(FunctionSymbol constant, StringBuilder builder) {
    builder.append("[");
    builder.append(constant.queryName());
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
   * function symbol, and which takes at least 1 argument.  This is NOT called for maximally applied
   * infix symbols; these are printed using printInfixTerm.
   *
   * The default functionality just calls printApplication.
   *
   * Note that functional terms with no arguments are printed through printConstant or
   * printSoloInfixSymbol instead.
   */
  protected void printFunctionalTerm(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                     StringBuilder builder) {
    printApplication(term, freeNaming, boundNaming, builder);
  }

  /**
   * Called by printRecursive() to print a base-type functional term f(s) where f is marked as an
   * infix symbol (so essentially, it is a prefix symbol).
   *
   * The default functionality simply prints f(s), so putting the arguments in brackets and not
   * adding extra spaces.
   *
   * Note that functional terms with an infix symbol as root but which are not fully applied
   * are printed through printFunctionalTerm or (if they have no arguments) through
   * printSoloInfixSymbol.  So a functional term f(s) with f an infix symbol but which does NOT have
   * base type would by default be printed as [f](s) instead of f(s).
   */
  protected void printPrefixTerm(FunctionSymbol root, Term arg, Renaming freeNaming,
                                 MutableRenaming boundNaming, StringBuilder builder) {
    builder.append(root.queryName());
    builder.append("(");
    printRecursive(arg, freeNaming, boundNaming, builder);
    builder.append(")");
  }

  /**
   * Called by printRecursive() to print a base-type functional term f(s1,...,sn) whose root symbol
   * is an infix symbol, and which has n ≥ 2.
   *
   * The default functionality prints s1 f ... f sn.  Each of the arguments si may be in brackets
   * if the root of si itself is also an infix symbol; this is then decided by
   * f.queryIncludeBrackets.  The printing of " f " itself is done through a call to
   * printInfixOperator.
   *
   * Note that functional terms with an infix symbol as root but which are not fully applied
   * are printed through printFunctionalTerm or (if they have no arguments) through
   * printSoloInfixSymbol.
   */
  protected void printInfixTerm(Term term, Renaming freeNaming, MutableRenaming boundNaming,
                                StringBuilder builder) {
    FunctionSymbol root = term.queryRoot();

    for (int i = 1; i <= term.numberArguments(); i++) {
      if (i > 1) printInfixOperator(root, i, builder);
      Term sub = term.queryArgument(i);
      boolean brackets = false;
      if (sub.isFunctionalTerm() && sub.queryRoot().isInfixSymbol() &&
          !sub.queryType().isArrowType()) {
        brackets = root.queryIncludeBrackets(sub.queryRoot(), i);
      }
      if (brackets) builder.append("(");
      printRecursive(sub, freeNaming, boundNaming, builder);
      if (brackets) builder.append(")");
    }
  }

  /**
   * Called by the default implementation of printInfixTerm to print the infix symbol f before
   * argument index (so index is at least 2).
   *
   * By default this just prints " f ", where f is the name of the symbol.
   */
  protected void printInfixOperator(FunctionSymbol f, int index, StringBuilder builder) {
    builder.append(" ");
    builder.append(f.queryName());
    builder.append(" ");
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
   * Called by printRecursive() to print an application where the head is not a function symbol or
   * variable, and called by the default implementation of printVarTerm and printFunctionalTerm to
   * print an application where the head is a function symbol or variable (with the exception of
   * base-type applications with the head an infix symbol, which are handled through the default
   * implementation of printInfixTerm.
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
}

