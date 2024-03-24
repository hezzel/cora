/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.reader;

import com.google.common.collect.ImmutableList;
import java.util.ArrayList;

import charlie.exceptions.*;
import charlie.types.*;
import charlie.parser.lib.Token;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.Parser.*;
import charlie.parser.CoraParser;
import charlie.terms.*;

/**
 * This class takes a ParserTerm, and turns it into a proper term -- assuming that it is
 * appropriately typed, and all its function symbols are declared in the symbol data.
 *
 * This class is not public, and mostly meant for inheriting by for instance the CoraInputReader.
 * It is default to support unit testing.
 */
class TermTyper {
  /**
   * The symbol data is used to keep track of the variables declared so far, as well as all the
   * declared function symbols.
   */
  protected SymbolData _symbols;

  /** When the term typer encounters errors, it stores them in this collector. */
  protected ErrorCollector _errors;

  /** The last token for which we stored an error. */
  protected Token _lastStored;

  /** Stores the symbol data and error collector for use by methods of the class. */
  public TermTyper(SymbolData data, ErrorCollector collector) {
    _symbols = data;
    _errors = collector;
    _lastStored = null;
  }

  protected void storeError(String message, Token token) {
    if (token == _lastStored) return;
    _errors.addError(token.getPosition() + ": " + message);
    _lastStored = token;
  }

  /**
   * This attempts to turn a ParserTerm into a Term, using that all function symbols are
   * necessarily declared in the symbol data.  If the given type is not null, then the term is
   * expected to be of that type (and this will be used to type previously unseen variables and
   * meta-variables).
   * If the given type is null, and the type cannot easily be derived (which is the case if the
   * term is a variable), then if typeShouldBeDerivable is set to true, an error is stored.  If
   * typeShouldBeDerivable is set to false, then the term is just given the default sort.
   * If function symbols are used with arity different from their declared arity, or types do not
   * match the declaration, then an appropriate error message is stored in the parser status.
   *
   * Regardless of errors, this is guaranteed to either throw a ParseError, or return a term of the
   * expected type (if any).
   */
  protected Term makeTerm(ParserTerm pt, Type expectedType, boolean typeShouldBeDerivable) {
    switch (pt) {
      case IntVal(Token t, int value):
        return confirmType(t, TheoryFactory.createValue(value), expectedType);
      case BoolVal(Token t, boolean isTrue):
        return confirmType(t, TheoryFactory.createValue(isTrue), expectedType);
      case StringVal(Token t, String txt):
        Term ret = null;
        try { ret = TheoryFactory.createEscapedStringValue(txt); }
        catch (IncorrectStringException e) {
          storeError(e.getMessage(), t);
          ret = TermFactory.createConstant(txt, TypeFactory.stringSort);
        }
        return confirmType(t, ret, expectedType);
      case CalcSymbol(Token t, String name):
        return makeCalculationSymbol(t, name, expectedType);
      case Identifier(Token t, String name):
        return makeIdentifier(t, name, expectedType, typeShouldBeDerivable);
      case Meta(Token t, String name, ImmutableList<ParserTerm> args):
        return makeMeta(t, name, args, expectedType, typeShouldBeDerivable);
      case Lambda(Token t, String varname, Type type, ParserTerm arg):
        return makeAbstraction(t, varname, type, arg, expectedType, typeShouldBeDerivable);
      case Tup(Token t, ImmutableList<ParserTerm> args):
        return makeTuple(t, args, expectedType, typeShouldBeDerivable);
      case Application(Token t, ParserTerm head, ImmutableList<ParserTerm> args):
        return makeApplication(t, head, args, expectedType, typeShouldBeDerivable);
      case PErr(ParserTerm t):
        return makeTerm(t, expectedType, typeShouldBeDerivable);
    }
  }

  /**
   * This checks if the term has the expected type, and if not, makes an alternative for nice
   * error messages which does have the epxected type.
   */
  private Term confirmType(Token token, Term term, Type expected) {
    if (expected == null || expected.equals(term.queryType())) return term;
    String kind = "term ";
    if (term.isValue()) kind = "value ";
    else if (term.isConstant()) kind = "function symbol ";
    else if (term.isVariable()) kind = "variable ";
    storeError("Expected term of type " + expected.toString() + ", but got " + kind +
      term.toString() + " which has type " + term.queryType().toString() + ".", token);
    return TermFactory.createConstant(term.toString(), expected);
  }

  private Term makeCalculationSymbol(Token token, String name, Type expected) {
    Term ret = switch (name) {
      case CoraParser.PLUS -> TheoryFactory.plusSymbol;
      case CoraParser.MINUS -> TheoryFactory.minusSymbol;
      case CoraParser.TIMES -> TheoryFactory.timesSymbol;
      case CoraParser.DIV -> TheoryFactory.divSymbol;
      case CoraParser.MOD -> TheoryFactory.modSymbol;
      case CoraParser.GREATER -> TheoryFactory.greaterSymbol;
      case CoraParser.SMALLER -> TheoryFactory.smallerSymbol;
      case CoraParser.GEQ -> TheoryFactory.geqSymbol;
      case CoraParser.LEQ -> TheoryFactory.leqSymbol;
      case CoraParser.EQUALS -> TheoryFactory.equalSymbol;
      case CoraParser.NEQ -> TheoryFactory.distinctSymbol;
      case CoraParser.AND -> TheoryFactory.andSymbol;
      case CoraParser.OR -> TheoryFactory.orSymbol;
      case CoraParser.NOT -> TheoryFactory.notSymbol;
      default -> null;
    };
    if (ret == null) { // this shouldn't happen: it's been created by the CoraParser
      throw new UnexpectedPatternError("TermTyper", "makeCalculationSymbol",
                                       "one of the known infix symbols", name);
    }
    // special case: what if someone gives [-] and intends it to be binary?
    if (expected != null && name.equals(CoraParser.MINUS) && expected.queryArity() == 2) {
      storeError("Use of unary calculation symbol [-] with binary type: while a - b is allowed " +
        "to occur in terms, this is considered syntactic sugar for a + (-b); it cannot be done " +
        "in a partially applied way.  If you want to use binary subtraction, please encode it " +
        "using a helper function symbol.", token);
      return TermFactory.createConstant("-", expected);
    }
    return confirmType(token, ret, expected);
  }

  /**
   * Turn a parserterm representing a function symbol or variable into the corresponding term,
   * but also store errors if we know it should have a different type from what is expected, or
   * is not derivable when it should be.
   */
  private Term makeIdentifier(Token token, String name, Type expected, boolean derivable) {
    FunctionSymbol f = _symbols.lookupFunctionSymbol(name);
    if (f != null) return confirmType(token, f, expected);
    Variable x = _symbols.lookupVariable(name);
    if (x != null) return confirmType(token, x, expected);
    if (_symbols.lookupMetaVariable(name) != null) {
      storeError("Symbol " + name + " was previously used (or declared) as a meta-variable with " +
        "arity > 0; here it is used as a variable.", token);
      if (expected == null) expected = _symbols.lookupMetaVariable(name).queryType();
      return TermFactory.createVar(name, expected);
    }
    if (expected == null) {
      if (derivable) {
        storeError("Undeclared symbol: " + name + ".  Type cannot easily be deduced from " +
          "context.", token);
      }
      return TermFactory.createVar(name);
    }
    x = TermFactory.createVar(name, expected);
    _symbols.addVariable(x);
    return x;
  }

  /**
   * Turn a ParserTerm representing a meta-application X[s1,...,sk] into the corresponding Term,
   * but also store errors if we know it should have a different type from what is expected, or is
   * not derivable when it should be, or if the arity does not match previous usage of this
   * meta-variable.
   */
  private Term makeMeta(Token token, String name, ImmutableList<ParserTerm> args, Type expected,
                        boolean typeShouldBeDerivable) {
    // no arguments are supplied -- it's actually a free variable
    if (args.size() == 0) return makeFreeVarTerm(token, name, expected, typeShouldBeDerivable);

    // option 1: we know it as a meta-variable
    MetaVariable mvar = _symbols.lookupMetaVariable(name);
    if (mvar != null) return makeKnownMetaTerm(token, mvar, args, expected);

    // eror option: we know it as something else
    if (_symbols.lookupFunctionSymbol(name) != null) {
      storeError("Unexpected meta-application with meta-variable " + name + ", which was " +
        "previously declared as a function symbol.", token);
    }
    else if (_symbols.lookupVariable(name) != null) {
      String kind = "variable without meta-arguments";
      if (_symbols.lookupVariable(name).isBinderVariable()) kind = "binder variable";
      storeError("Unexpected meta-application with meta-variable " + name + ", which was " +
        "previously used (or declared) as a " + kind +".", token);
    }
    // error option: we don't know what type it should be
    if (expected == null && typeShouldBeDerivable) {
      storeError("Cannot derive output type of meta-variable " + name + " from context.", token);
    }

    // option 2: we don't know it yet, so we get to declare it
    ArrayList<Term> targs = new ArrayList<Term>();
    ArrayList<Type> types = new ArrayList<Type>();
    for (int i = 0; i < args.size(); i++) {
      Term targ = makeTerm(args.get(i), null, typeShouldBeDerivable);
      targs.add(targ);
      types.add(targ.queryType());
    }
    mvar = TermFactory.createMetaVar(name, types,
                                     expected == null ? TypeFactory.defaultSort : expected);
    if (expected != null) _symbols.addMetaVariable(mvar);
    return TermFactory.createMeta(mvar, targs);
  }

  /**
   * Turn a parserterm representing a meta-application with no arguments X[] into the
   * corresponding Term, but also stores errors as needed.
   */
  private Term makeFreeVarTerm(Token token, String name, Type expected, boolean deriveType) {
    // we know it as a variable
    Variable ret = _symbols.lookupVariable(name);
    if (ret != null) {
      if (ret.isBinderVariable()) {
        storeError("Binder variable " + name + " used as meta-variable.", token);
      }
      if (expected == null || expected.equals(ret.queryType())) return ret;
      storeError("Expected term of type " + expected.toString() + ", but got " + name +
        ", which was previously used as a variable of type " + ret.queryType() + ".", token);
      return TermFactory.createVar(name, expected);
    }
    boolean declare = expected != null;
    // we know it as a meta-variable, which means a higher type -- store a suitable error
    if (_symbols.lookupMetaVariable(name) != null) {
      storeError("Meta-application for meta-variable " + name + " has no arguments, when it " +
        "previously occurred (or was declared) with arity " +
        _symbols.lookupMetaVariable(name).queryArity() + ".", token);
      if (expected == null) expected = _symbols.lookupMetaVariable(name).queryType();
      declare = false;
    }
    // we know it as a function symbol -- give a suitable error
    else if (_symbols.lookupFunctionSymbol(name) != null) {
      storeError("Meta-application for meta-variable " + name + ", which was previously " +
        "declared as a function symbol.", token);
      if (expected == null) expected = _symbols.lookupFunctionSymbol(name).queryType();
      declare = false;
    }
    // regardless of errors: if we don't know it we get to create it as a free variable now
    if (expected != null) {
      Variable x = TermFactory.createVar(name, expected);
      if (declare) _symbols.addVariable(x);
      return x;
    }
    // unfortunately, if we can't figure out the type, we just assign a default
    if (deriveType) {
      storeError("Undeclared (meta-)variable: " + name + ".  Type cannot easily be deduced " +
        "from context.", token);
    }
    return TermFactory.createVar(name);
  }

  /**
   * This function handles a ParserTerm mvar[children], when mvar has already been declared.
   */
  private Term makeKnownMetaTerm(Token token, MetaVariable mvar, ImmutableList<ParserTerm> children,
                                 Type expected) {

    ArrayList<Term> args = new ArrayList<Term>();
    if (mvar.queryArity() == children.size()) {
      for (int i = 0; i < children.size(); i++) {
        args.add(makeTerm(children.get(i), mvar.queryInputType(i+1), true));
      }
      if (expected == null || expected.equals(mvar.queryOutputType())) {
        return TermFactory.createMeta(mvar, args);
      }
    }

    // error case: the children size does not match the previous / declared occurrence
    else {
      storeError("Meta-variable " + mvar.queryName() + " was previously used (or declared) " +
        "with arity " + mvar.queryArity() + ", but is here used with " + children.size() +
        " arguments.", token);
      for (int i = 0; i < children.size(); i++) args.add(makeTerm(children.get(i), null, false));
    }

    // error case: the output type does not match the previous / declared occurrence
    if (expected != null && !expected.equals(mvar.queryOutputType())) {
      storeError("Meta-variable " + mvar.queryName() + " has output type " +
        mvar.queryOutputType().toString() + " while a term of type " + expected.toString() +
        " was expected.", token);
    }

    // in either error case, create a new meta-variable with the right input and output types
    ArrayList<Type> types = new ArrayList<Type>();
    for (int i = 0; i < args.size(); i++) types.add(args.get(i).queryType());
    if (expected == null) expected = mvar.queryOutputType();
    mvar = TermFactory.createMetaVar(mvar.queryName(), types, expected);
    return TermFactory.createMeta(mvar, args);
  }

  /**
   * Turn a ParserTerm representing a tuple into the corresponding term, and check that it matches
   * the epxected type; if not, then it is wrapped to ensure that the return value has the
   * expected type. (If expected == null, any type suffices.)
   */
  private Term makeTuple(Token token, ImmutableList<ParserTerm> elems, Type expected,
                         boolean typeShouldBeDerivable) {
    // handle the correct case first
    if (elems.size() >= 2 && (expected == null ||
        (expected.isProductType() && expected.numberSubtypes() == elems.size()))) {
      ArrayList<Term> parts = new ArrayList<Term>();
      for (int i = 0; i < elems.size(); i++) {
        Type exp = expected == null ? null : expected.subtype(i+1);
        parts.add(makeTerm(elems.get(i), exp, typeShouldBeDerivable));
      }
      return TermFactory.createTuple(parts);
    }

    // handle the error cases!
    if (elems.size() == 0) {
      storeError("Illegal empty tuple: tuples should have at least length 2.", token);
      return TermFactory.createConstant("⦇⦈", expected == null ? TypeFactory.defaultSort : expected);
    }
    if (elems.size() == 1) {
      storeError("Illegal singleton tuple: tuples should have at least length 2.", token);
      return makeTerm(elems.get(0), expected, typeShouldBeDerivable);
    }

    // now we know expected != null, and there's a type problem
    if (!expected.isProductType()) {
      storeError("Type error: expected a term of type " + expected.toString() + " but got a " +
        "tuple, which necessarily has a product type.", token);
    }
    else {
      storeError("Type error: expected a term of type " + expected.toString() + " but got a " +
        "tuple of length " + elems.size() + ".", token);
    }

    ArrayList<Term> parts = new ArrayList<Term>();
    for (int i = 0; i < elems.size(); i++) parts.add(makeTerm(elems.get(i), null, false));
    Term ret = TermFactory.createTuple(parts);
    return TermFactory.createConstant(ret.toString(), expected);
  }

  /**
   * Turn a parserterm representing an abstraction into the corresponding term, and check that it
   * matches the expected type; if no expected type is given, then the binder should have a type
   * denotation, and the type of the subterm derivable.
   */
  private Term makeAbstraction(Token token, String varname, Type vartype, ParserTerm arg,
                               Type expected, boolean typeShouldBeDerivable) {
    Type expectedSubtype = null;

    // special error case: if we have no idea what the type of the binder could be, we'll just do
    // the type derivation without it (which results in the binder being treated as a free variable
    // in the subterm)
    if (expected == null && vartype == null) {
      if (typeShouldBeDerivable) {
        storeError("Cannot derive type of binder " + varname + " from context; it should be " +
          "denoted directly in the abstraction.", token);
      }
      Term subterm = makeTerm(arg, null, false);
      return TermFactory.createAbstraction(TermFactory.createBinder(varname,
        TypeFactory.defaultSort), subterm);
    }

    // special error case: we are not expecting an arrow type
    if (expected != null && !expected.isArrowType()) {
      storeError("Type error: expected subterm of type " + expected.toString() + ", but got " +
        "abstraction, which necessarily has an arrow type.", token);
      Term ret = makeAbstraction(token, varname, vartype, arg, null, false);
      Type helper = TypeFactory.createArrow(ret.queryType(), expected);
      FunctionSymbol wrapper = TermFactory.createConstant("abs", helper);
      return wrapper.apply(ret);
    }

    Type einp = null, eout = null;
    if (expected != null) { einp = expected.subtype(1); eout = expected.subtype(2); }

    // in all other cases, we either have the type of the binder, or can derive it
    if (vartype == null) vartype = einp;
    else if (expected != null && !vartype.equals(einp)) {
      storeError("Type error: expected subterm of type " + expected.toString() +
        ", but got abstraction with variable of type " + vartype.toString() + ".", token);
      vartype = einp;
    }

    // generate the variable and store it in the environment
    Variable tmp = _symbols.lookupVariable(varname);
    if (tmp != null) _symbols.removeVariable(varname);
    if (_symbols.lookupFunctionSymbol(varname) != null) {
      storeError("Ambiguous binder: this name has already been declared as a function symbol.",
        token);
    }
    else if (_symbols.lookupMetaVariable(varname) != null) {
      storeError("Ambiguous binder: this name has already been declared as a meta-variable.",
        token);
    }
    Variable binder = TermFactory.createBinder(varname, vartype);
    _symbols.addVariable(binder);

    // read the subterm
    Term subterm = makeTerm(arg, eout, true);

    // clean up and return the abstraction
    _symbols.removeVariable(varname);
    if (tmp != null) _symbols.addVariable(tmp);
    return TermFactory.createAbstraction(binder, subterm);
  }

  /**
   * Turn a ParserTerm representing an application into the corresponding term, and check that
   * it matches the expected type.  We require that the term at the head of an application can
   * always figure out its own type, so the expected type is only used for checking here.
   */
  private Term makeApplication(Token token, ParserTerm apphead, ImmutableList<ParserTerm> args,
                               Type expected, boolean typeShouldBeDerivable) {
    Term head = makeTerm(apphead, null, true);
    if (head.equals(TheoryFactory.minusSymbol)) {
      return makeMinusApplication(token, args, expected);
    }
    if (head.queryType().queryArity() >= args.size()) {
      for (int i = 0; i < args.size(); i++) {
        Term arg = makeTerm(args.get(i), head.queryType().subtype(1), true);
        head = head.apply(arg);
      }
      if (expected == null || head.queryType().equals(expected)) return head;
    }

    // error handling: what if the type of head does not have the right arity?
    else {
      storeError("Arity error: " + head.toString() + " has type " + head.queryType().toString() +
        ", but " + args.size() + " arguments are given.", token);
      // read arguments
      ArrayList<Term> parts = new ArrayList<Term>();
      for (int i = 0; i < args.size(); i++) parts.add(makeTerm(args.get(i), null, false));
      // make type that head _should_ have
      Type type = (expected == null) ? head.queryType().queryOutputType() : expected;
      for (int i = parts.size()-1; i >= 0; i--) {
        type = TypeFactory.createArrow(parts.get(i).queryType(), type);
      }
      // create a fake term of the right type
      Term start = TermFactory.createConstant(head.toString(), type);
      return TermFactory.createApp(start, parts);
    }

    // remaining case: head had the right arity, but the resulting term did not have the right type
    storeError("Type error: expected term of type " + expected.toString() + ", but got " +
      head.toString() + " of type " + head.queryType() + ".", token);
    return TermFactory.createConstant(head.toString(), expected);
  }

  /**
   * Turn a parserterm [-](args) into the corresponding term, and check that it matches the
   * expected type.  This is a bit of a special case, because the minus can both be used in binary
   * and unary form, and sometimes even to construct an integer.
   * Here, args.size() 
   */
  private Term makeMinusApplication(Token token, ImmutableList<ParserTerm> args, Type expected) {
    if (args.size() == 0) return makeCalculationSymbol(token, CoraParser.MINUS, expected);
    ArrayList<Term> targs = new ArrayList<Term>();
    for (int i = 0; i < args.size(); i++) {
      targs.add(makeTerm(args.get(i), TypeFactory.intSort, true));
    }
    if (args.size() == 1) {
      Term child = targs.get(0);
      if (child.isValue()) {
        return confirmType(token, TheoryFactory.createValue(-child.toValue().getInt()), expected);
      }
      return confirmType(token, TheoryFactory.minusSymbol.apply(targs.get(0)), expected);
    }
    if (args.size() == 2) {
      Term a = targs.get(0);
      Term b = targs.get(1);
      if (b.isValue()) b = TheoryFactory.createValue(-b.toValue().getInt());
      else b = TheoryFactory.minusSymbol.apply(b);
      return confirmType(token, TermFactory.createApp(TheoryFactory.plusSymbol, a, b), expected);
    }
    storeError("Arity error: [-] can be used either with 1 or 2 arguments, but here it occurs " +
      "with " + args.size() + ".", token);
    Type type = expected == null ? TypeFactory.intSort : expected;
    for (int i = targs.size()-1; i >= 0; i--) {
      type = TypeFactory.createArrow(targs.get(i).queryType(), type);
    }
    Term fakehead = TermFactory.createConstant("[-]", type);
    return TermFactory.createApp(fakehead,targs);
  }

  // ============================== ACCESS FUNCTIONS FOR UNIT TESTING =============================

  /** Parses the given term using the given parsing data. */
  static Term readTerm(String str, boolean constrained, SymbolData data, Type expected,
                       ErrorCollector collector) {
    ParserTerm pt = CoraParser.readTerm(str, constrained, collector);
    Term ret = null;
    if (!pt.hasErrors()) {
      TermTyper typer = new TermTyper(data, collector);
      ret = typer.makeTerm(pt, expected, true);
    }
    return ret;
  }
}
