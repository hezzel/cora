/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.printer;

import java.util.Arrays;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import charlie.util.Pair;
import charlie.util.UserException;
import charlie.types.Type;
import charlie.types.TypePrinter;
import charlie.terms.position.Position;
import charlie.terms.position.PositionPrinter;
import charlie.terms.replaceable.Replaceable;
import charlie.terms.replaceable.Renaming;
import charlie.terms.replaceable.MutableRenaming;
import charlie.terms.*;
import charlie.trs.Rule;
import charlie.trs.TRS;

/**
 * In Charlie, it is generally not advised to use toString() for any information that is printed to
 * an end user (the function should show _reasonable_ output, but only for the sake of IDE output,
 * unit testing and debugging).  This is for multiple reasons:
 * - There is a lot of unicode in Charlie which the user output might not actually support.
 * - Moreover, Charlie output may end up in various places, such as a GUI or webpage.  In those
 *   places, various symbols need to be printed differently, even a relatively innocuous symbol
 *   like >.
 * - Term printing is also complex due to the possibility of multiple (meta-)variables having the
 *   same name (which in particular may occur after some transformations, or lambda-reductions).
 *   For this reason, printing temrs is subject to a Renaming.  In order to print the same variable
 *   by the same name in multiple terms within a string, it is important to consistently use the
 *   same Renaming.
 *
 * The Printer is designed to handle this issue.  A Printer functions largely like a StringBuilder:
 * a class to gradually build a string.  However, a critical difference is that there are multiple
 * kinds of Printers (and additional special-purpose ones may be defined), which have in-built
 * functionality for printing specific kinds of objects:
 * - There are multiple functions defining mathematical symbols.  The actual returned string
 *   depends on the kind of printer.  For example, to add ⊢ to an existing printer, you would use:
 *   printer.add(printer.symbVdash());  As Printer is an abstract class, the inheriting class will
 *   define how this is printed, for example in unicode (⊢), plain text (|-), latex (\vdash) or
 *   html (&#x22A2;)
 * - The Printer carries Type, Term and Position printers, allowing the user to print such objects
 *   directly without having to worry about invoking the relevant sub-printer.
 * - The Printer also knows how to print Rules, as well as any class that implements
 *   PrintableObject, in an appropriate way for the given Printer.
 *
 * After building a Printer, just use toString() to get the resulting string.
 */
public abstract class Printer {
  protected StringBuilder _builder;
  protected TypePrinter _typePrinter;
  protected TermPrinter _termPrinter;
  protected PositionPrinter _posPrinter;

  protected Printer(TypePrinter typr, TermPrinter tepr, PositionPrinter popr) {
    _typePrinter = typr;
    _termPrinter = tepr;
    _posPrinter = popr;
    _builder = new StringBuilder();
  }

  /** This returns the TypePrinter used for printing types in this OutputModule. */
  public final TypePrinter queryTypePrinter() { return _typePrinter; }

  /**
   * This returns the TermPrinter used for printing terms in this OutputModule.  It is also used to
   * generated renamings.
   */
  public final TermPrinter queryTermPrinter() { return _termPrinter; }

  /** This returns the PositionPrinter used for printing positions in this OutputModule. */
  public final PositionPrinter queryPositionPrinter() { return _posPrinter; }

  /**
   * This uses the underlying TermPrinter to generate a Renaming that takes all the variables (and
   * meta-variables) in the given terms into account.
   */
  public final MutableRenaming generateUniqueNaming(Term ...terms) {
    return _termPrinter.generateUniqueNaming(Arrays.asList(terms));
  }

  /**
   * This uses the underlying TermPrinter to generate a Renaming that takes all the variables (and
   * meta-variables) in the given terms into account.
   */
  public final MutableRenaming generateNaming(List<Term> terms) {
    return _termPrinter.generateUniqueNaming(terms);
  }

  /**
   * Returns false if anything has been printed to the Printer (since creation or since the last
   * clear).
   */
  public final boolean isEmpty() {
    return _builder.length() == 0;
  }

  /** This sets the current contents of the current printer to "". */
  public final void clear() {
    _builder.setLength(0);
  }

  /**
   * Returns the string that we have built so far.  It is still possible to continue printing after
   * using toString().
   */
  public final String toString() {
    return _builder.toString();
  }

  public abstract String symbRuleArrow();
  public abstract String symbTypeArrow();
  public abstract String symbMapsto();
  public abstract String symbThickArrow();
  public abstract String symbLongArrow();
  public abstract String symbDownArrow();
  public abstract String symbRevRuleArrow();

  public abstract String symbVdash();
  public abstract String symbVDash();
  public abstract String symbForall();
  public abstract String symbExists();
  public abstract String symbAnd();
  public abstract String symbOr();
  public abstract String symbNot();
  public abstract String symbImplies();
  public abstract String symbIff();

  public abstract String symbEmptySet();
  public abstract String symbUnion();
  public abstract String symbSubterm();
  public abstract String symbSubtermeq();
  public abstract String symbSupterm();
  public abstract String symbSuptermeq();

  public abstract String symbSqSupset();
  public abstract String symbSqSupseteq();
  public abstract String symbSucc();
  public abstract String symbSucceq();
  public abstract String symbGreater();
  public abstract String symbSmaller();
  public abstract String symbGeq();
  public abstract String symbLeq();
  public abstract String symbLangle();
  public abstract String symbRangle();
  public abstract String symbDistinct();
  public abstract String symbApprox();

  public abstract String symbSharp();
  public abstract String symbBullet();
  public abstract String symbStar();

  public abstract String symbAlpha();
  public abstract String symbBeta();
  public abstract String symbGamma();
  public abstract String symbDelta();
  public abstract String symbEpsilon();
  public abstract String symbZeta();
  public abstract String symbEta();
  public abstract String symbTheta();
  public abstract String symbIota();
  public abstract String symbKappa();
  public abstract String symbLambda();
  public abstract String symbMu();
  public abstract String symbNu();
  public abstract String symbXi();
  public abstract String symbPi();
  public abstract String symbRho();
  public abstract String symbSigma();
  public abstract String symbTau();
  public abstract String symbPhi();
  public abstract String symbChi();
  public abstract String symbPsi();
  public abstract String symbOmega();

  /**
   * The core method of the printer: add text to it.  The text is a list of objects, which are
   * printed as follows:
   * - Strings and integers are printed directly.
   * - Type objects are printed using the underlying Type printer
   * - Position objects are printed using the underlying Position printer
   * - for Term objects, a fresh Renaming is generated that includes the (meta-)variables of all
   *   Terms that are passed in args, and they are printed using the underlying Term printer
   *   with this Renaming
   * - for Rule objects, a fresh Renaming is generated that includes the (meta-)variables of both
   *   the left-hand side, right-hand side and constraint, and they are printed using the
   *   underlying Term Printer with this Renaming
   * - any object that implements PrintableObject is asked to print itself
   * - for any Object[] or List, the add function is called recursively
   * - for a UserException, the add function is called recursively (representing the underlying
   *   components as an Object[])
   * - for an object Pair<Term,Renaming>, we print the term using the underlying TermPrinter with
   *   the given Renaming
   * - for an object Pair<Rule,Renaming>, we print the rule using the underlying TermPrinter with
   *   the given Renaming
   * - for an object Pair<Substitution,Renaming>, we print the substitution using the underlying
   *   TermPrinter, with both keys and values using the same given Renaming (a substitution cannot
   *   be printed without a Renaming, because a substitution refers to some other terms in which
   *   at least the keys occur, so it would be meaningless to generate a fresh renaming for the
   *   keys)
   * - any other objects are printed through ob.toString()
   *
   * Note that the Term objects are printed in such a way that occurrences of the same variables in
   * multiple terms (in the given object list) are all printed with the same name, and this name is
   * only used for ONE variable.  However, this only holds for objects in the same list.  So for
   * example, if you have terms s and t, which are both variables with a name set to "x", then
   * printer.add(s, " ", t) will return in something like "x__1 x__2" being stored, while
   * printer.add(s, " "); printer.add(t) will result in "x x".  Similarly, printer.add(List.of(s),
   * " ", List.of(t)) will also yield "x x".  Any Rules that may occur in the same call to add are
   * also printed with their own Renaming, so if we have a rule t -> 0, then Printer.add(s, " ",
   * rule) will yield "x x -> 0".
   *
   * Note: if you pass a Pair<Term,Renaming> as one of the Object arguments instead of just a term,
   * then this will lead to the given term being printed with the given Renaming, and not being
   * considered for the naming of other terms in the given list.  Hence, if there is a need to
   * print terms across multiple calls to add using the same Renaming, then the calling method can
   * use this to do so (but needs to keep track of the Renaming by itself).  The same works for a
   * Pair<Rule,Renaming>.
   */
  public final void add(Object ...objects) {
    storeRenaming(objects);
    for (Object ob : objects) printSingleObject(ob);
  }

  /** 
   * This helper function for add finds a renaming for all the terms in the given object list, and
   * updates the list to make the terms include the renaming.
   */
  private final void storeRenaming(Object[] objects) {
    ArrayList<Term> terms = new ArrayList<Term>();
    for (int i = 0; i < objects.length; i++) {
      if (objects[i] instanceof Term t) terms.add(t);
      else if (objects[i] instanceof Replaceable r) terms.add(TermFactory.makeTerm(r));
    }   
    Renaming renaming = _termPrinter.generateUniqueNaming(terms);
    for (int i = 0; i < objects.length; i++) {
      if (objects[i] instanceof Term t) objects[i] = new Pair<Term,Renaming>(t, renaming);
      else if (objects[i] instanceof Replaceable r) {
        objects[i] = new Pair<Replaceable,Renaming>(r, renaming);
      }
    }
  }

  /**
   * This helper function for add adds a string representation for a single object to the
   * underlying string builder.
   * When this is called by the add function, ob is guaranteed not to be a single Term: all Terms
   * have already been paired with a Renaming by storeRenaming.
   */
  protected final void printSingleObject(Object ob) {
    switch (ob) {
      case Object[] o: add(o); break;
      case List a: add(a.toArray()); break;
      case UserException e: add(e.makeArray()); break;
      case String s: _builder.append(s); break;
      case Integer i: _builder.append(i.toString()); break;
      case Type y: _typePrinter.print(y, _builder); break;
      case Position p: _posPrinter.print(p, _builder); break;
      case Rule r: printRule(r, null); break;
      case PrintableObject o: o.print(this); break;
      // supplied in case something other than the add function is calling us
      case Term t: _termPrinter.print(t, _builder); break;
      default:
        if (ob instanceof Pair p && p.snd() instanceof Renaming renaming) {
          if (p.fst() instanceof Term t) _termPrinter.print(t, renaming, _builder);
          else if (p.fst() instanceof Rule rule) printRule(rule, renaming);
          else if (p.fst() instanceof Substitution sub) printSubstitution(sub, renaming, renaming);
          else if (p.fst() instanceof Replaceable r) {
            _termPrinter.printReplaceable(r, renaming, _builder);
          }
          else printSingleUnknownObject(ob);
        }
        else printSingleUnknownObject(ob);
    }
  }

  /**
   * Helper function for printSingleObject: stores a string representation for the given rule in
   * the underlying string builder, taking into account the given renaming.
   * If the renaming is null, then a suitable renaming will be generated.
   *
   * This function may be masked to print rules in a different way, but inheriting classes should
   * take into account that renaming might be null!
   */
  protected void printRule(Rule rho, Renaming renaming) {
    if (renaming == null) {
      renaming = _termPrinter.generateUniqueNaming(rho.queryLeftSide(), rho.queryRightSide(),
                                                   rho.queryConstraint());
    }
    _termPrinter.print(rho.queryLeftSide(), renaming, _builder);
    _builder.append(" " + symbRuleArrow() + " ");
    _termPrinter.print(rho.queryRightSide(), renaming, _builder);
    if (rho.isConstrained()) {
      _builder.append(" | ");
      _termPrinter.print(rho.queryConstraint(), renaming, _builder);
    }
  }

  /**
   * Helper function for printSingleObject: this stores a string representation for the given
   * substitution, with (meta-)variable names for the domain taken from keyNaming, and the names
   * for the values taken from valueNaming.
   *
   * This function may be masked to print substitutions in a different way.
   */
  protected void printSubstitution(Substitution gamma, Renaming keyNaming, Renaming valueNaming) {
    // put the names in a list, so we can order them
    ArrayList<Pair<Replaceable,String>> dom = new ArrayList<Pair<Replaceable,String>>();
    for (Replaceable x : gamma.domain()) {
      String xname = keyNaming.getName(x);
      if (xname == null) {
        throw new IllegalArgumentException("KeyNaming given to printSubstitution does not have " +
          "a mapping for " + x.queryName() + "(" + x.queryIndex() + ").");
      }
      dom.add(new Pair<Replaceable,String>(x, xname));
    }
    Collections.sort(dom, (x,y) ->
      x.fst().queryReplaceableKind() == y.fst().queryReplaceableKind() ? x.snd().compareTo(y.snd())
                        : x.fst().queryReplaceableKind().compareTo(y.fst().queryReplaceableKind()));

    // print the lot
    _builder.append("[");
    for (int i = 0; i < dom.size(); i++) {
      if (i > 0) _builder.append(", ");
      _builder.append(dom.get(i).snd());
      _builder.append(" := ");
      _termPrinter.print(gamma.get(dom.get(i).fst()), valueNaming, _builder);
    }
    _builder.append("]");
  }

  public class PrintingUnknownObjectException extends RuntimeException {
    private PrintingUnknownObjectException(Object ob) {
      super("Asked to print object of type " + ob.getClass().getName() + ", which is not " +
        "supported by the default Printer.");
    }

    private PrintingUnknownObjectException(Object ob1, Object ob2) {
      super("Asked to print object of type Pair<" + ob1.getClass().getName() + "," +
        ob2.getClass().getName() + ">, which is not supported by the default Printer.");
    }
  }

  /**
   * Called by printSingleObject if an object appears in the object list that uses a class we do
   * not know.  By default, this throws a PrintingUnknownObjectException, but may be masked to
   * support additional objects or even to just print ob.toString() (though doing the latter may
   * hide incorrect calls to the printer).
   */
  protected void printSingleUnknownObject(Object ob) {
    if (ob instanceof Pair p) throw new PrintingUnknownObjectException(p.fst(), p.snd());
    else throw new PrintingUnknownObjectException(ob);
  }

  /**
   * This creates a wrapper for a substitution with two renamings: one for the keys, and one for
   * the values.  These two renamings are allowed to, but do not have to, be the same.  The
   * printable object prints substitutions taking these renamings into account.  (Note that
   * substitutions cannot be printed without a given renaming).
   *
   * Note that all replaceables in the domain of the substitution must be listed in keys, and it
   * is highly recommended that all replaceables occurring in the range of the substitution are in
   * values.
   *
   * Note also that the printable object stores the reference to the substitution.  So  if you
   * change the substitution after you create the object, but before you actually print it, then
   * the object printed will be the updated substitution! (And the renamings should reflect this.)
   */
  public static PrintableObject makePrintable(Substitution subst, Renaming keys,
                                              Renaming values) {
    return new PrintableObject() {
      public void print(Printer p) {
        p.printSubstitution(subst, keys, values);
      }
    };
  }

  /**
   * This creates a wrapper for a rule with a renaming.  While rules can be printed directly
   * through the add function, this causes a fresh renaming to be generated, and when printing
   * rules to the user, you may wish to have some control over how the variables are printed.
   * This object ensures that the rule is printed with the variables named as expected.  Note
   * that all variables occurring in the rule should occur in the renaming!
   */
  public static PrintableObject makePrintable(Rule rule, Renaming renaming) {
    return new PrintableObject() {
      public void print(Printer p) {
        p.printRule(rule, renaming);
      }
    };
  }

  /**
   * This creates a wrapper for a term with a fixed renaming.  Printing this printable object is
   * equivalent to printing the pair (t,renaming).
   */
  public static PrintableObject makePrintable(Term term, Renaming renaming) {
    return new PrintableObject() {
      public void print(Printer p) {
        p._termPrinter.print(term, renaming, p._builder);
      }
      public String toString() {
        return (new TermPrinter(Set.of())).print(term, renaming);
      }
    };
  }

  /**
   * This creates a wrapper for a user exception where a fixed renaming is to be used for the terms
   * occuring in its components.
   */
  public static PrintableObject makePrintable(UserException e, Renaming renaming) {
    return new PrintableObject() {
      public void print(Printer p) {
        Object[] objects = e.makeArray();
        for (int i = 0; i < objects.length; i++) {
          if (objects[i] instanceof Term t) objects[i] = new Pair<Term,Renaming>(t, renaming);
          else if (objects[i] instanceof Replaceable r) {
            objects[i] = new Pair<Replaceable,Renaming>(r, renaming);
          }
        }
        p.add(objects);
      }
      public String toString() {
        TermPrinter pr = new TermPrinter(Set.of());
        StringBuilder builder = new StringBuilder();
        Object[] objects = e.makeArray();
        for (int i = 0; i < objects.length; i++) {
          if (objects[i] instanceof Term t) pr.print(t, renaming, builder);
          else if (objects[i] instanceof Replaceable r) pr.printReplaceable(r, renaming, builder);
          else builder.append(objects[i].toString());
        }
        return builder.toString();
      }
    };
  }
}

