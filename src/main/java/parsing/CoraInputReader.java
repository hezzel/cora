/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.parsing;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import cora.exceptions.*;
import cora.parsing.lib.Token;
import cora.parsing.lib.TokenQueue;
import cora.parsing.lib.ParsingStatus;
import cora.types.*;
import cora.terms.*;
import cora.rewriting.*;

class TermStructure {
  static int CONSTANT = 1;
  static int VARIABLE = 2;
  static int META = 3;
  static int ABSTRACTION = 4;
  static int APPLICATION = 5;

  Token token;                        // the token starting this term
  int kind;                           // one of the five kinds above
  FunctionSymbol symbol;              // for constant (a declared symbol)
  String str;                         // for string or meta
  TermStructure head;                 // for application
  ArrayList<TermStructure> children;  // for meta, application or abstraction
  Type vartype;                       // for abstractions with typed binder
  boolean errored;

  TermStructure(Token t, int k) {
    token = t;
    kind = k;
    symbol = null;
    str = null;
    head = null;
    children = null;
    vartype = null;
    errored = false;
  }   

  /** for debugging purposes */
  public String toString() {
    String ret = "(" + kind + ":";
    if (str != null) ret += "\"" + str + "\"";
    if (symbol != null) ret += "!" + symbol.toUniqueString() + "!";
    if (head != null) ret += "{" + head.toString() + "}";
    if (children != null) {
      ret += "[";
      for (int i = 0; i < children.size(); i++) ret += children.get(i).toString() + ";";
      ret += "]";
    }
    ret += (errored ? "ERR" : "");
    return ret + ")";
  }
}

/** This class reads text from string or file written in the internal .cora format. */
public class CoraInputReader {
  public static int MSTRS = 1;
  public static int STRS = 2;
  public static int CFS = 3;
  public static int AMS = 4;
  public static int LCTRS = 5;
  public static int DEFAULT = 6;

  /**
   * The reader keeps track of the status of reading so far; all read functions have a (potential)
   * side effect of advancing the parsing status.
   */
  private ParsingStatus _status;
  /**
   * The reader keeps track of the declared variables, and the function symbols encountered so far.
   */
  private SymbolData _symbols;

  /**
   * Stores the parsing status for use by methods of the CoraInputReader class.
   * Private because it should only be called by the static methods that use a CoraInputReader.
   */
  private CoraInputReader(ParsingStatus status) {
    _status = status;
    _symbols = new SymbolData();
  }

  /**
   * Stores the parsing status for use by methods of the CoraInputReader class, and stores the
   * given TRS into the SymbolData used to parse terms.
   * Private because it should only be called by the static methods that use a CoraInputReader.
   */
  private CoraInputReader(ParsingStatus status, TRS trs) {
    _status = status;
    _symbols = new SymbolData(trs);
  }

  // ===================================== PARSING CONSTANTS ======================================

  /**
   * This function checks if the next tokens represent a string, and if so, returns the string.
   * If not, null is returned and nothing is read.
   */
  private String tryReadIdentifier() {
    Token next = _status.readNextIf(CoraTokenData.IDENTIFIER);
    if (next != null) return next.getText();
    return null;
  }

  // ======================================== READING TYPES =======================================

  /**
   * typearrow := TYPEARROW | ARROW
   *
   * This function checks if the next token is one of the two arrows that may be used for types,
   * and if so, reads it and returns true.  If not, false is returned instead.
   *
   * If a RULEARROW is given instead, then it will also be read (since a rule arrow should never
   * occur at the place of a type arrow), but an error is stored.
   */
  private boolean tryReadTypeArrow() {
    if (_status.readNextIf(CoraTokenData.TYPEARROW) != null) return true;
    if (_status.readNextIf(CoraTokenData.ARROW) != null) return true;
    // error handling
    Token token = _status.readNextIf(CoraTokenData.RULEARROW);
    if (token != null) {
      _status.storeError("Rule arrow → occurs in a type; did you mean ⇒?", token);
      return true;
    }
    return false;
  }

  /**
   * sort ::= INTTYPE | BOOLTYPE | STRINGTYPE | IDENTIFIER
   *
   * This function attempts to read a sort, and returns it.  If there is no sort at the start of
   * the input, then nothing is read and null is returned.
   */
  private BaseType tryReadSort() {
    if (_status.readNextIf(CoraTokenData.INTTYPE) != null) return TypeFactory.intSort;
    if (_status.readNextIf(CoraTokenData.BOOLTYPE) != null) return TypeFactory.boolSort;
    if (_status.readNextIf(CoraTokenData.STRINGTYPE) != null) return TypeFactory.stringSort;
    String name = tryReadIdentifier();
    if (name == null) return null;
    return TypeFactory.createSort(name);
  }

  /**
   * type ::= constant (typearrow type)?
   *        | BRACKETOPEN type BRACKETCLOSE (typearrow type)?
   *
   * This function reads a type and returns it.
   * The input is expected to actually be a type. If this is not the case, then an error is stored.
   * If some kind of error recovery could be done, a Type is still returned; otherwise, null may be
   * returned, even if something was read -- indicating that we will have to do large-scale error
   * recovery.
   */
  private Type readType() {
    Type start = tryReadSort();
    if (start == null) {
      Token bracket = _status.expect(CoraTokenData.BRACKETOPEN,
        "a type (started by a sort identifier or bracket)");
      if (bracket == null) { // error recovery
        if (tryReadTypeArrow()) return readType();  // maybe we have -> type or () -> type
        return null;                                // otherwise, no idea what they're trying to do
      }
      start = readType();
      if (_status.expect(CoraTokenData.BRACKETCLOSE, "closing bracket") == null) return start;
    }

    if (!tryReadTypeArrow()) return start;
    
    Type end = readType();
    if (start == null) return end;
    if (end == null) return start;
    return TypeFactory.createArrow(start, end);
  }

  // =================================== READING TERM STRUCTURES ==================================

  /**
   * term = abstraction
   *      | mainterm (infixsymbol mainterm)*
   *
   * When the current parsing status represents a term, this method reads it into a term structure,
   * which does not yet check correct typing / arity use of the term.  If null is returned, parsing
   * failed beyond the point where we could do error recovery.
   */
  private TermStructure readTermStructure() {
    if (_status.nextTokenIs(CoraTokenData.LAMBDA)) return readAbstractionStructure();

    TermStructure struc = readMainTermStructure();
    if (struc == null) return null;
    Token optoken = _status.peekNext();
    CalculationSymbol op = tryReadInfixSymbol();
    if (op == null) return struc;

    Stack<TermStructure> left = new Stack<TermStructure>();
    left.push(struc);
    Stack<CalculationSymbol> operator = new Stack<CalculationSymbol>();
    operator.push(op);
    Stack<Token> operatorToken = new Stack<Token>();
    operatorToken.push(optoken);

    while (true) {
      struc = readMainTermStructure();
      if (struc == null) break;
      optoken = _status.peekNext();
      op = tryReadInfixSymbol();
      if (op == null) break;
      while (!operator.empty()) {
        if (op.queryInfixPriority() < operator.peek().queryInfixPriority() ||
            op.equals(operator.peek())) {
          struc = combineInfix(left, operator, operatorToken, struc);
        }
        else if (op.queryInfixPriority() == operator.peek().queryInfixPriority()) {
          _status.storeError("Ambiguous priorities in parser: no clear priority has been set " +
            "between " + operator.peek() + " (at " + operatorToken.peek().getPosition() + ") " +
            "and " + op.toString() + ".", optoken);
          struc = combineInfix(left, operator, operatorToken, struc);
        }
        else break;
      }
      left.push(struc);
      operator.push(op);
      operatorToken.push(optoken);
    }

    if (struc == null) { // error case
      struc = left.pop();
      operator.pop();
      operatorToken.pop();
      struc.errored = true;
    }

    while (!operator.empty()) struc = combineInfix(left, operator, operatorToken, struc);
    return struc;
  }

  /** Given a term s, returns the term -s, where the token for - is given. */
  private TermStructure negate(TermStructure struct, Token minustoken) {
    if (struct.kind == TermStructure.CONSTANT &&
        struct.symbol.isValue() &&
        struct.symbol.queryType().equals(TypeFactory.intSort)) {
      struct.symbol = TermFactory.createValue(-struct.symbol.toValue().getInt());
      return struct;
    }

    TermStructure head = new TermStructure(minustoken, TermStructure.CONSTANT);
    head.symbol = TermFactory.createMinus();
    TermStructure ret = new TermStructure(minustoken, TermStructure.APPLICATION);
    ret.head = head;
    ret.children = new ArrayList<TermStructure>();
    ret.children.add(struct);
    ret.errored = struct.errored;
    return ret;
  }

  /**
   * Given that all the stacks have at least one argument, this will make the termstructure:
   * operator.pop() ( left.pop(), struct), marked for token operatorToken.pop().
   */
  private TermStructure combineInfix(Stack<TermStructure> left, Stack<CalculationSymbol> operator,
                                     Stack<Token> operatorToken, TermStructure struct) {
    Token token = operatorToken.pop();
    // a - has been treated as a +, but we still need to negate the argument
    if (token.getName().equals(CoraTokenData.MINUS)) struct = negate(struct, token);
    TermStructure root = new TermStructure(token, TermStructure.CONSTANT);
    root.symbol = operator.pop();
    TermStructure ret = new TermStructure(root.token, TermStructure.APPLICATION);
    ret.head = root;
    ret.children = new ArrayList<TermStructure>();
    ret.children.add(left.pop());
    ret.children.add(struct);
    ret.errored = struct.errored;
    return ret;
  }

  /**
   * mainterm = value
   *          | IDENTIFIER
   *          | IDENTIFIER METAOPEN termlist METACLOSE
   *          | mainterm BRACKETOPEN termlist BRACKETCLOSE
   *          | BRACKETOPEN term BRACKETCLOSE
   *          | NOT mainterm
   *          | MINUS mainterm
   */
  private TermStructure readMainTermStructure() {
    TermStructure ret;

    // NOT mainterm
    if (_status.nextTokenIs(CoraTokenData.NOT)) {
      Token token = _status.nextToken();
      ret = new TermStructure(token, TermStructure.APPLICATION);
      ret.children = new ArrayList<TermStructure>();
      ret.head = new TermStructure(token, TermStructure.CONSTANT);
      ret.head.symbol = TermFactory.createNot();
      TermStructure tmp = readMainTermStructure();
      if (tmp == null) ret.errored = true;
      else {
        ret.errored = tmp.errored;
        ret.children.add(tmp);
      }
      return ret;
    }

    // MINUS mainterm
    if (_status.nextTokenIs(CoraTokenData.MINUS)) {
      Token token = _status.nextToken();
      TermStructure main = readMainTermStructure();
      return negate(main, token);
    }

    // value
    if (_status.nextTokenIs(CoraTokenData.STRING) ||
        _status.nextTokenIs(CoraTokenData.INTEGER) ||
        _status.nextTokenIs(CoraTokenData.TRUE) ||
        _status.nextTokenIs(CoraTokenData.FALSE)) {
      ret = readValueStructure();
    }
    // BRACKETOPEN term BRACKETCLOSE  -- we store term as ret
    else if (_status.readNextIf(CoraTokenData.BRACKETOPEN) != null) {
      ret = readTermStructure();
      if (ret == null) { _status.readNextIf(CoraTokenData.BRACKETCLOSE); return null; }
      if (_status.expect(CoraTokenData.BRACKETCLOSE, "a closing bracket") == null) {
        ret.errored = true;
        return ret;
      }
    }
    // IDENTIFIER
    else {
      Token token = _status.expect(CoraTokenData.IDENTIFIER, "term, started by an identifier, " +
        "λ, string or (,");
      if (token == null) return null;
      Token next;
      // IDENTIFIER METAOPEN termlist METACLOSE
      if ((next = _status.readNextIf(CoraTokenData.METAOPEN)) != null) {
        ret = new TermStructure(token, TermStructure.META);
        ret.str = token.getText();
        readTermList(ret, CoraTokenData.METACLOSE, "meta-closing bracket " +
          (next.getText().equals("[") ? "]" : "⟩"));
      }
      else {
        // just IDENTIFIER (so a constant or variable)
        FunctionSymbol f = _symbols.lookupFunctionSymbol(token.getText());
        if (f == null) {
          ret = new TermStructure(token, TermStructure.VARIABLE);
          ret.str = token.getText();
        }
        else {
          ret = new TermStructure(token, TermStructure.CONSTANT);
          ret.symbol = f;
        }
      }
    }

    // if we see an argument list, read it, and make the application structure
    while (_status.readNextIf(CoraTokenData.BRACKETOPEN) != null) {
      TermStructure app = new TermStructure(ret.token, TermStructure.APPLICATION);
      app.head = ret;
      readTermList(app, CoraTokenData.BRACKETCLOSE, "closing bracket )");
      ret = app;
    }

    return ret;
  }

  /**
   * abstraction ::= LAMBDA vardec (COMMA vardec)* DOT term
   *
   * where
   * vardec ::= IDENTIFIER
   *          | IDENTIFIER DECLARE type
   */
  private TermStructure readAbstractionStructure() {
    // read λ
    if (_status.expect(CoraTokenData.LAMBDA, "a λ") == null) return null;
    boolean errored = false;

    // read every (name,type) combination into (variables,type); when type is not given, this
    // component is simply left null
    ArrayList<Token> tokens = new ArrayList<Token>();
    ArrayList<String> variables = new ArrayList<String>();
    ArrayList<Type> types = new ArrayList<Type>();
    while (true) {
      String name = null;
      Type type = null;

      Token token = _status.expect(CoraTokenData.IDENTIFIER, "an identifier (variable name)");
      if (token != null) name = token.getText();
      if (_status.readNextIf(CoraTokenData.DECLARE) != null) {
        type = readType();
        if (type == null) errored = true;
      }

      if (name != null) {
        tokens.add(token);
        variables.add(name);
        types.add(type);
      }
      else errored = true;
      
      // stop reading once we encounter a .
      if (_status.readNextIf(CoraTokenData.DOT) != null) break;
      // following an identifier and a type, the only alternative is a comma; if this is not
      // supplied, we either continue reading anyway (after giving an error), or abort if there are
      // no more variable names to come
      if (_status.expect(CoraTokenData.COMMA, "a comma or dot") == null) {
        if (!_status.nextTokenIs(CoraTokenData.IDENTIFIER)) { errored = true; break; }
      }
    }
    // we read LAMBDA vardec (COMMA vardec)* DOT, so now just read the term (which extends as far
    // as it can)
    TermStructure ret = readTermStructure();
    if (ret == null) return null;

    // put everything together
    for (int i = variables.size()-1; i >= 0; i--) {
      TermStructure tmp = new TermStructure(tokens.get(i), TermStructure.ABSTRACTION);
      tmp.str = variables.get(i);
      tmp.vartype = types.get(i);
      tmp.children = new ArrayList<TermStructure>();
      tmp.children.add(ret);
      ret = tmp;
      ret.errored = errored;
    }
    return ret;
  }

  /**
   * value = STRING+ | INT | TRUE | FALSE
   *
   * This function is really only called when we already know the next token is a string, int, or
   * boolean constant, so should not fail.  In the case of strings, it eagerly reads as many
   * strings as are available.
   */
  private TermStructure readValueStructure() {
    Token token = _status.nextToken();
    TermStructure ret = new TermStructure(token, TermStructure.CONSTANT);

    if (token.getName().equals(CoraTokenData.TRUE)) ret.symbol = TermFactory.createValue(true);
    else if (token.getName().equals(CoraTokenData.FALSE)) {
      ret.symbol = TermFactory.createValue(false);
    }
    else if (token.getName().equals(CoraTokenData.INTEGER)) {
      try {
        int number = Integer.parseInt(token.getText());
        ret.symbol = TermFactory.createValue(number);
      }
      catch (NumberFormatException e) {
        _status.storeError(e.getMessage(), token);
        ret.symbol = TermFactory.createConstant(token.getText(), TypeFactory.intSort);
      }
    }
    else if (token.getName().equals(CoraTokenData.STRING)) {
      // take the token's text without the closing "
      StringBuilder text =
        new StringBuilder(token.getText().substring(0, token.getText().length()-1));
      Token next;
      while ( (next = _status.readNextIf(CoraTokenData.STRING)) != null) {
        // for each subsequent string, append it without quotes
        text.append(next.getText().substring(1, next.getText().length()-1));
      }
      // append a final quote to make sure the string is well-formed
      text.append("\"");
      try {
        ret.symbol = TermFactory.createEscapedStringValue(text.toString());
      }
      catch (IncorrectStringException e) {
        _status.storeError(e.getMessage(), token);
        ret.symbol = TermFactory.createConstant(token.getText(), TypeFactory.stringSort);
      }
    }
    else throw new Error("Calling readValueStructure when it shouldn't be.");

    return ret;
  }

  /**
   * Returns true if it should be possible to read at least one token towards a term structure in
   * the current status.
   */
  private boolean nextMayBeTerm() {
    return _status.nextTokenIs(CoraTokenData.LAMBDA) ||
           _status.nextTokenIs(CoraTokenData.STRING) ||
           _status.nextTokenIs(CoraTokenData.INTEGER) ||
           _status.nextTokenIs(CoraTokenData.TRUE) ||
           _status.nextTokenIs(CoraTokenData.FALSE) ||
           _status.nextTokenIs(CoraTokenData.BRACKETOPEN) ||
           _status.nextTokenIs(CoraTokenData.IDENTIFIER);
  }

  /** 
   * termlist ::= ε [followName] | term (COMMA term)* [followName]
   *
   * The terms are read into the "children" field of the given structure.
   */
  private void readTermList(TermStructure struc, String followName, String followDescription) {
    Token token;
    struc.children = new ArrayList<TermStructure>();

    // handle the case ε [followName]
    if (_status.readNextIf(followName) != null) return;

    // read the arguments until we encounter [followName] or we're in an overly weird place
    while (true) {
      // appropriate error handling if we see commas where there shouldn't be
      if ((token = _status.readNextIf(CoraTokenData.COMMA)) != null) {
        _status.storeError("Unexpected comma; expected term or " + followDescription, token);
        struc.errored = true;
        while (_status.readNextIf(CoraTokenData.COMMA) != null);
      }
      // read the next term in the list
      TermStructure arg = readTermStructure();
      if (arg == null) struc.errored = true;
      else struc.children.add(arg);
      if (_status.readNextIf(followName) != null) return;
      if (_status.expect(CoraTokenData.COMMA, "a comma or " + followDescription) == null) {
        // we recover from a missing comma, but only if we're still followed by another term
        struc.errored = true;
        if (!nextMayBeTerm()) return;
      }
    }
  }

  /**
   * If the next token is an infix operator, this function reads it and returns the corresponding
   * CalculationSymbol.  If not, nothing is read and null is returned.
   * NOTE: when reading a minus, the PLUS symbol is returned, since a - b is treated like a + -b.
   * The calling function should take care of this if the given token is a minus.
   */
  private CalculationSymbol tryReadInfixSymbol() {
    if (_status.readNextIf(CoraTokenData.PLUS) != null) return TermFactory.createPlus();
    if (_status.readNextIf(CoraTokenData.TIMES) != null) return TermFactory.createTimes();
    if (_status.readNextIf(CoraTokenData.AND) != null) return TermFactory.createAnd();
    if (_status.readNextIf(CoraTokenData.OR) != null) return TermFactory.createOr();
    if (_status.readNextIf(CoraTokenData.GREATER) != null) return TermFactory.createGreater();
    if (_status.readNextIf(CoraTokenData.SMALLER) != null) return TermFactory.createSmaller();
    if (_status.readNextIf(CoraTokenData.GEQ) != null) return TermFactory.createGeq();
    if (_status.readNextIf(CoraTokenData.LEQ) != null) return TermFactory.createLeq();
    // a minus is treated as a plus
    if (_status.readNextIf(CoraTokenData.MINUS) != null) return TermFactory.createPlus();
    return null;
  }

  // ============================ TURNING A TERM STRUCTURE INTO A TERM ============================

  /**
   * This attempts to turn a TermStructure into a Term, using that all function symbols are
   * necessarily declared in the symbol data.  If the given type is not null, then the term is
   * expected to be of that type (and this will be used to type previously unseen variables and
   * meta-variables).
   * If the given type is null, and the type cannot easily be derived (which is the case if the
   * term is a variable), then if typeShouldBeDerivable is set to true, an error is stored.  If
   * typeShouldBeDerivable is set to false, then the term is just given the unit sort as a default.
   * If function symbols are used with arity different from their declared arity, or types do not
   * match the declaration, then an appropriate error message is stored in the parser status.
   *
   * Regardless of errors, this is guaranteed to either throw a ParseError, or return a term of the
   * expected type (if any).
   */
  private Term makeTerm(TermStructure structure, Type expectedType, boolean typeShouldBeDerivable) {
    if (structure.kind == TermStructure.CONSTANT) return makeConstantTerm(structure, expectedType);
    if (structure.kind == TermStructure.VARIABLE) {
      return makeVariableTerm(structure, expectedType, typeShouldBeDerivable);
    }
    if (structure.kind == TermStructure.META) {
      return makeMetaTerm(structure, expectedType, typeShouldBeDerivable);
    }
    if (structure.kind == TermStructure.ABSTRACTION) {
      return makeAbstractionTerm(structure, expectedType);
    }
    if (structure.kind == TermStructure.APPLICATION) return makeApplTerm(structure, expectedType);
    throw new Error("Unexpected term structure: " + structure.kind);
  }

  /**
   * Turn a term structure representing a known function symbol into the corresponding term, but
   * also set an error if the expected type is not the type of the function
   */
  private Term makeConstantTerm(TermStructure structure, Type expectedType) {
    if (structure == null || structure.symbol == null) {  // shouldn't happen
      throw new Error("Called makeConstantTerm when structure is null!");
    }
    if (expectedType == null || expectedType.equals(structure.symbol.queryType())) {
      return structure.symbol;
    }
    _status.storeError("Expected term of type " + expectedType.toString() + ", but got " +
      (structure.symbol.isValue() ? "value " : "function symbol ") +
      structure.symbol.toString() + " which has type " + structure.symbol.queryType().toString()
      + ".", structure.token);
    return TermFactory.createConstant(structure.symbol.queryName(), expectedType);
  }

  /**
   * Turn a termstructure representing a variable (an identifier that is not declared as a function
   * symbol) into the corresponding term, but also throw errors if we know it should have a
   * different type from what is expected, or is not derivable when it should be
   */
  private Term makeVariableTerm(TermStructure structure, Type expectedType, boolean deriveType) {
    String name = structure.str;
    if (name == null) {  // shouldn't happen
      throw new Error("Called makeVariableTerm when the variable is not stored in str!");
    }
    // we have seen this variable before, or it's declared in our current context
    Term ret = _symbols.lookupVariable(name);
    if (ret != null) {
      if (expectedType == null || expectedType.equals(ret.queryType())) return ret;
      _status.storeError("Expected term of type " + expectedType.toString() + ", but got " +
        name + ", which was previously used as a variable of type " + ret.queryType() + ".",
        structure.token);
      return TermFactory.createVar(name, expectedType);
    }
    // we know it as a meta-variable, so it shouldn't be used in this way
    if (_symbols.lookupMetaVariable(name) != null) {
      _status.storeError("Symbol " + name + " was previously used (or declared) as a " +
        "meta-variable with arity > 0; here it is used as a variable.", structure.token);
      if (expectedType == null) expectedType = _symbols.lookupMetaVariable(name).queryType();
    }
    // we don't know it, but we know the type so we can declare it as a free variable
    if (expectedType != null) {
      Variable x = TermFactory.createVar(name, expectedType);
      _symbols.addVariable(x);
      return x;
    }
    // we don't know it, and can't deduce its type
    if (deriveType) {
      _status.storeError("Undeclared symbol: " + name + ".  Type cannot easily be deduced from " +
      "context.", structure.token);
    }
    return TermFactory.createVar(name, TypeFactory.unitSort);
  }

  /**
   * Turn a termstructure representing a meta-application X[s1,...,sk] into the corresponding Term,
   * but also throw errors if we know it should have a different type from what is expected, or is
   * not derivable when it should be, or if the arity does not match previous usage of this
   * meta-variable.
   */
  private Term makeMetaTerm(TermStructure structure, Type expectedType, boolean deriveType) {
    String name = structure.str;
    if (name == null) { // shouldn't happen
      throw new Error("Called makeMetaTerm when the meta-variable name is not stored in str!");
    }
    // no arguments are supplied -- it's actually a free variable
    if (structure.children.size() == 0) {
      return makeFreeVarTerm(structure.token, name, expectedType, deriveType);
    }

    // option 1: we know it as a meta-variable
    MetaVariable mvar = _symbols.lookupMetaVariable(name);
    if (mvar != null) {
      return makeKnownMetaTerm(structure.token, mvar, structure.children, expectedType);
    }

    // eror option: we know it as something else
    if (_symbols.lookupFunctionSymbol(name) != null) {
      _status.storeError("Unexpected meta-application with meta-variable " + name + ", which " +
        "was previously declared as a function symbol.", structure.token);
    }
    else if (_symbols.lookupVariable(name) != null) {
      String kind = "variable without meta-arguments";
      if (_symbols.lookupVariable(name).isBinderVariable()) kind = "binder variable";
      _status.storeError("Unexpected meta-application with meta-variable " + name + ", which " +
        "was previously used (or declared) as a " + kind +".", structure.token);
    }
    // error option: we don't know what type it should be
    if (expectedType == null) {
      if (deriveType) {
        _status.storeError("Cannot derive output type of meta-variable " + name + " from context.",
          structure.token);
      }
    }

    // option 2: we don't know it yet, so we get to declare it
    ArrayList<Term> args = new ArrayList<Term>();
    ArrayList<Type> types = new ArrayList<Type>();
    for (int i = 0; i < structure.children.size(); i++) {
      Term arg = makeTerm(structure.children.get(i), null, deriveType);
      args.add(arg);
      types.add(arg.queryType());
    }
    mvar = TermFactory.createMetaVar(name, types,
                                     expectedType == null ? TypeFactory.unitSort : expectedType);
    if (expectedType != null) _symbols.addMetaVariable(mvar);
    return TermFactory.createMeta(mvar, args);
  }

  /**
   * Turn a termstructure representing a meta-application with no arguments X[] into the
   * corresponding Term, but also throws errors as needed.
   */
  private Term makeFreeVarTerm(Token token, String name, Type expectedType, boolean deriveType) {
    // we know it as a variable
    Variable ret = _symbols.lookupVariable(name);
    if (ret != null) {
      if (ret.isBinderVariable()) {
        _status.storeError("Binder variable " + name + " used as meta-variable.", token);
      }
      if (expectedType == null || expectedType.equals(ret.queryType())) return ret;
      _status.storeError("Expected term of type " + expectedType.toString() + ", but got " +
        name + ", which was previously used as a variable of type " + ret.queryType() + ".",
        token);
      return TermFactory.createVar(name, expectedType);
    }
    // we know it as a meta-variable, which means a higher type -- give a suitable error
    if (_symbols.lookupMetaVariable(name) != null) {
      _status.storeError("Meta-application for meta-variable " + name + " has no arguments, when " +
        "it previously occurred (or was declared) with arity " +
        _symbols.lookupMetaVariable(name).queryArity(), token);
      if (expectedType == null) expectedType = _symbols.lookupMetaVariable(name).queryType();
    }
    // we know it as a function symbol -- give a suitable error
    else if (_symbols.lookupFunctionSymbol(name) != null) {
      _status.storeError("Meta-application for meta-variable " + name + ", which was previously " +
        "declared as a function symbol.", token);
      if (expectedType == null) expectedType = _symbols.lookupFunctionSymbol(name).queryType();
    }
    // regardless of errors: if we don't know it we get to create it as a free variable now
    if (expectedType != null) {
      Variable x = TermFactory.createVar(name, expectedType);
      _symbols.addVariable(x);
      return x;
    }
    // unfortunately, if we can't figure out the type, we just assign a default
    if (deriveType) {
      _status.storeError("Undeclared (meta-)variable: " + name + ".  Type cannot easily be " +
        "deduced from context.", token);
    }
    return TermFactory.createVar(name, TypeFactory.unitSort);
  }

  /**
   * This function handles a term structure mvar[children], when mvar has already been declared.
   */
  private Term makeKnownMetaTerm(Token token, MetaVariable mvar, ArrayList<TermStructure> children,
                                 Type expectedType) {

    ArrayList<Term> args = new ArrayList<Term>();
    if (mvar.queryArity() == children.size()) {
      for (int i = 0; i < children.size(); i++) {
        args.add(makeTerm(children.get(i), mvar.queryInputType(i+1), true));
      }
      if (expectedType == null || expectedType.equals(mvar.queryOutputType())) {
        return TermFactory.createMeta(mvar, args);
      }
    }

    // error case: the children size does not match the previous / declared occurrence
    else {
      _status.storeError("Meta-variable " + mvar.queryName()+ " was previously used (or " +
        "declared) with arity " + mvar.queryArity() + ", but is here used with " +
        children.size() + " arguments.", token);
      for (int i = 0; i < children.size(); i++) args.add(makeTerm(children.get(i), null, false));
    }

    // error case: the output type does not match the previous / declared occurrence
    if (expectedType != null && !expectedType.equals(mvar.queryOutputType())) {
      _status.storeError("Meta-variable " + mvar.queryName() + " has output type " +
        mvar.queryOutputType().toString() + " while a term of type " + expectedType.toString() +
        " was expected.", token);
    }

    // in either error case, create a new meta-variable with the right input and output types
    ArrayList<Type> types = new ArrayList<Type>();
    for (int i = 0; i < args.size(); i++) types.add(args.get(i).queryType());
    if (expectedType == null) expectedType = mvar.queryOutputType();
    mvar = TermFactory.createMetaVar(mvar.queryName(), types, expectedType);
    return TermFactory.createMeta(mvar, args);
  }

  /**
   * Turn a term structure representing an abstraction into the corresponding term, and check that
   * it matches the expected type; if no expected type is given, then the binder should have a type
   * denotation, and the type of the subterm derivable.
   */
  private Term makeAbstractionTerm(TermStructure structure, Type expectedType) {
    String varname = structure.str;
    Type type = structure.vartype;
    Type expectedSubtype = null;

    // special error case: if we have no idea what the type of the binder could be, we'll just do
    // the type derivation without it (which results in the binder being treated as a free variable
    // in the subterm)
    if (expectedType == null && type == null) {
      _status.storeError("Cannot derive type of binder " + varname + " from " +
        "context; it should be denoted directly in the abstraction.", structure.token);
      Term subterm = makeTerm(structure.children.get(0), null, false);
      return TermFactory.createAbstraction(TermFactory.createBinder(varname,
        TypeFactory.unitSort), subterm);
    }

    // in all other cases, we either have the type of the binder, or can derive it
    if (type == null) type = expectedType.queryArrowInputType();
    else if (expectedType != null && !type.equals(expectedType.queryArrowInputType())) {
      _status.storeError("Type error: expected subterm of type " + expectedType.toString() +
        ", but got abstraction with variable of type " + type.toString() + ".", structure.token);
      type = expectedType.queryArrowInputType();
    }

    // generate the variable and store it in the environment
    Variable tmp = _symbols.lookupVariable(varname);
    if (tmp != null) _symbols.removeVariable(varname);
    if (_symbols.lookupFunctionSymbol(varname) != null) {
      _status.storeError("Ambiguous binder: this name has already been declared as a function " +
        "symbol.", structure.token);
    }
    else if (_symbols.lookupMetaVariable(varname) != null) {
      _status.storeError("Ambiguous binder: this name has already been declared as a " +
        "meta-variable.", structure.token);
    }
    else if (tmp != null && !tmp.isBinderVariable()) {
      _status.storeError("Ambiguous binder: this name has already been declared as a " +
        "free variable.", structure.token);
    }
    Variable binder = TermFactory.createBinder(varname, type);
    _symbols.addVariable(binder);

    // read the subterm
    Term subterm = makeTerm(structure.children.get(0),
                            expectedType == null ? null : expectedType.queryArrowOutputType(),
                            true);

    // clean up and return the abstraction
    _symbols.removeVariable(varname);
    if (tmp != null) _symbols.addVariable(tmp);
    return TermFactory.createAbstraction(binder, subterm);
  }

  /**
   * Turn a term structure representing an application into the corresponding term, and check that
   * it matches the expected type.  We require that the term at the head of an application can
   * always figure out its own type, so the expected type is only used for checking here.
   */
  private Term makeApplTerm(TermStructure structure, Type expectedType) {
    Term head = makeTerm(structure.head, null, true);
    if (head.queryType().queryArity() >= structure.children.size()) {
      for (int i = 0; i < structure.children.size(); i++) {
        Term arg =
          makeTerm(structure.children.get(i), head.queryType().queryArrowInputType(), true);
        head = head.apply(arg);
      }
      if (expectedType == null || head.queryType().equals(expectedType)) return head;
    }

    // error handling: what if the type of head does not have the right arity?
    else {
      _status.storeError("Arity error: " + head.toString() + " has type " +
        head.queryType().toString() + ", but " + structure.children.size() +
        " arguments are given.", structure.token);
      // read children
      ArrayList<Term> args = new ArrayList<Term>();
      for (int i = 0; i < structure.children.size(); i++) {
        args.add(makeTerm(structure.children.get(i), null, false));
      }
      // make type that head _should_ have
      Type type = (expectedType == null) ? head.queryType().queryOutputSort() : expectedType;
      for (int i = args.size()-1; i >= 0; i--) {
        type = TypeFactory.createArrow(args.get(i).queryType(), type);
      }
      // create a fake term of the right type
      Term start = TermFactory.createConstant(head.toString(), type);
      return TermFactory.createApp(start, args);
    }

    // remaining case: head had the right arity, but the resulting term did not have the right type
    _status.storeError("Type error: expected term of type " + expectedType.toString() + ", but " +
      "got " + head.toString() + " of type " + head.queryType() + ".", structure.token);
    return TermFactory.createConstant(head.toString(), expectedType);
  }

  // ==================================== READING ENVIRONMENTS ====================================

  /**
   * environment ::= BRACEOPEN BRACECLOSE
   *               | BRACEOPEN mdeclaration (COMMA mdeclaration)* BRACECLOSE
   */
  private void readEnvironment() {
    if (_status.expect(CoraTokenData.BRACEOPEN, "environment opening brace {") == null) return;
    if (_status.readNextIf(CoraTokenData.BRACECLOSE) != null) return;  // BRACEOPEN BRACECLOSE
    while (true) {
      readMetaVariableDeclaration();
      if (_status.readNextIf(CoraTokenData.BRACECLOSE) != null) return;
      if (_status.expect(CoraTokenData.COMMA, "comma or }") == null) {
        if (!readRecoverEnvironment().getName().equals(CoraTokenData.COMMA)) return;
      }
    }
  }

  /**
   * mdeclaration ::= IDENTIFIER DECLARE type
   *                | IDENTIFIER DECLARE METAOPEN METACLOSE typearrow type
   *                | IDENTIFIER DECLARE METAOPEN type (COMMA type)* METACLOSE typearrow type
   */
  private void readMetaVariableDeclaration() {
    Token token = _status.expect(CoraTokenData.IDENTIFIER, "a variable or meta-variable name");
    Token decl = _status.expect(CoraTokenData.DECLARE, "declare symbol (::)");
    if (token == null && decl == null) return;

    // METAOPEN METACLOSE typearrow or
    // METAOPEN type (COMMA type)* METACLOSE typearrow
    ArrayList<Type> args = new ArrayList<Type>();
    if (_status.readNextIf(CoraTokenData.METAOPEN) != null) {
      if (_status.readNextIf(CoraTokenData.METACLOSE) == null) {
        while (true) {
          Type type = readType();
          if (type != null) args.add(type);
          if (_status.readNextIf(CoraTokenData.METACLOSE) != null) break;
          if (_status.expect(CoraTokenData.COMMA, "comma or ] or ⟩") == null) {
            if (type == null) return; // no idea where we are now, probably try recovery
          }
        }
      }
      if (!tryReadTypeArrow()) {
        Token tok = _status.peekNext();
        _status.storeError("Unexpected token: " + tok.getText() + " (" + tok.getName() + "); " +
          "expected type arrow ⇒.", tok);
      }
    }

    Type type = readType();
    if (type == null) return;

    // make sure the symbol is new
    String name = token.getText();
    String kind = args.size() == 0 ? "variable" : "meta-variable";
    if (_symbols.lookupFunctionSymbol(name) != null) {
      _status.storeError("Name of " + kind + " " + name + " already occurs as a function symbol.",
                         token);
    }
    else if (_symbols.symbolDeclared(name)) {
      _status.storeError("Redeclaration of " + kind + " " + name + " in the same environment.",
                         token);
    }
    // and if so, declare it!
    else {
      if (args.size() == 0) _symbols.addVariable(TermFactory.createVar(name, type));
      else _symbols.addMetaVariable(TermFactory.createMetaVar(name, args, type));
    }
  }

  /**
   * We have encountered an error in an environment, and will now continue reading until the next
   * token is a COMMA, BRACEOPEN, BRACECLOSE, or the end of a file.
   *
   * If it is BRACEOPEN or EOF, then the token is not read; if it is COMMA or BRACECLOSE, it is.
   * The final token is returned.
   */
  private Token readRecoverEnvironment() {
    Token next = _status.nextToken();
    while (!next.isEof() && !next.getName().equals(CoraTokenData.COMMA) &&
           !next.getName().equals(CoraTokenData.BRACEOPEN) &&
           !next.getName().equals(CoraTokenData.BRACECLOSE)) next = _status.nextToken();
    if (!next.getName().equals(CoraTokenData.COMMA) &&
        !next.getName().equals(CoraTokenData.BRACECLOSE)) _status.pushBack(next);
    return next;
  }

  // ====================================== READING PROGRAMS ======================================

  /**
   * This function recovers from a broken state, by reading until we come to something that is
   * likely to be the start of a program line again.
   */
  private void recoverState() {
    Token prev = null, curr = null;
    boolean intype = true;    // set if there's any possibility we're inside a type
    while (true) {
      prev = curr;
      curr = _status.nextToken();
      if (curr.isEof()) return;
      // { <-- we're at the start of a rule
      if (curr.getName().equals(CoraTokenData.BRACEOPEN)) { _status.pushBack(curr); return; }
      // } <-- we're past the rule declaration part, but still at the start of a rule; we're just
      // probably going to run into typing trouble, but so be it
      if (curr.getName().equals(CoraTokenData.BRACECLOSE)) { _status.pushBack(curr); return; }
      // :: <-- we may be a token into a declaration; if it's not a function symbol declaration
      // but a variable declaration, tryReadDeclaration has recovery functionality built in so we
      // don't get illicit declarations
      if (curr.getName().equals(CoraTokenData.DECLARE) && prev != null &&
          prev.getName().equals(CoraTokenData.IDENTIFIER)) {
        _status.pushBack(curr);
        _status.pushBack(prev);
        return;
      }
      // ( or [ <-- if this comes directly after an identifier, we are not in a type
      if ((curr.getName().equals(CoraTokenData.BRACKETOPEN) ||
           curr.getName().equals(CoraTokenData.METAOPEN)) &&
          prev != null && prev.getName().equals(CoraTokenData.IDENTIFIER)) {
        intype = false;
      }
      // . <-- we're after a lambda declaration, so no longer in a type at least
      if (curr.getName().equals(CoraTokenData.DOT)) intype = false;
      // ⇒ <-- whatever we thought before, we are definitely reading a type
      if (curr.getName().equals(CoraTokenData.TYPEARROW)) intype = true;
      // → or -> when we're not in a type <-- we're before the right-hand side of a rule
      if (curr.getName().equals(CoraTokenData.RULEARROW) ||
          (curr.getName().equals(CoraTokenData.ARROW) && !intype)) {
        TermStructure str = readTermStructure();
        if (str != null) return;
      }
    }
  }

  /**
   * declaration ::= IDENTIFIER DECLARE type
   *
   * A declaration for a symbol in the alphabet is immediately saved into the symbol data.  However,
   * to avoid storing something that was actually meant to be part of an abstraction or variable
   * declaration (with the user making errors), we also check if it is not followed by , or . or }
   * before storing the declaration, to improve error recovery.
   *
   * If the upcoming two tokens are not IDENTIFIER DECLARE, then nothing is read and false returned.
   * In all other cases, true is returned, and at least two tokens are read.
   * If the type cannot be properly read, then error recovery is immediately done to get back to a
   * program line.
   */
  private boolean tryReadDeclaration() {
    Token constant = _status.readNextIf(CoraTokenData.IDENTIFIER);
    if (constant == null) return false;
    if (_status.readNextIf(CoraTokenData.DECLARE) == null) {
      _status.pushBack(constant);
      return false;
    }
    Type type = readType();
    if (_status.nextTokenIs(CoraTokenData.BRACECLOSE)) return true;
    if (_status.nextTokenIs(CoraTokenData.COMMA) || _status.nextTokenIs(CoraTokenData.DOT) ||
        type == null) {
      recoverState();
      return true;
    }

    String name = constant.getText();
    if (_symbols.lookupFunctionSymbol(name) != null) {
      _status.storeError("Redeclaration of previously declared function symbol " + name + ".",
                         constant);
    }
    else _symbols.addFunctionSymbol(TermFactory.createConstant(name, type));
    return true;
  }

  /**
   * rulearrow := RULEARROW | ARROW
   *
   * This function checks if the next token is one of the two arrows that may be used for rules,
   * and if so, reads it and returns true.  If not, false is returned instead and an error stored.
   *
   * If a TYPEARROW is given instead, then it will also be read (since a type arrow should never
   * occur at the place of a rule arrow) and true returned, but an error is still stored.
   */
  private boolean readRuleArrow() {
    Token token;
    if (_status.readNextIf(CoraTokenData.RULEARROW) != null) return true;
    if ((token = _status.readNextIf(CoraTokenData.TYPEARROW)) != null) {
      _status.storeError("Encountered unexpected type arrow ⇒; please use → for rules.", token);
      return true;
    }
    return _status.expect(CoraTokenData.ARROW, "a rule arrow →, or ascii arrow ->") != null;
  }

  /**
   * rule ::= environment? term rulearrow term
   *
   * When reading a rule, variables and meta-variables are refreshed because these differ for every
   * rule.  If reading a term structure fails, we immediately do error recovery, to return to a
   * state where the next rule or declaraiton can be read.
   */
  private Rule readRule() {
    _symbols.clearEnvironment();
    Token start = _status.peekNext();
    if (_status.nextTokenIs(CoraTokenData.BRACEOPEN)) readEnvironment();
    // this could happen due to error recovery, but means we should stop trying to read this rule
    if (_status.nextTokenIs(CoraTokenData.BRACEOPEN)) return null;
    TermStructure left = readTermStructure();
    boolean ok = readRuleArrow();
    TermStructure right = ok ? readTermStructure() : null;

    if (left != null && right != null && !left.errored && !right.errored) {
      Term l = makeTerm(left, null, true);
      Term r = makeTerm(right, l.queryType(), false);
      try { return RuleFactory.createRule(l, r); }
      catch (IllegalRuleError e) {
        _status.storeError(e.queryProblem(), start);
        return null;
      }
    }

    // error recovery: the structures aren't right
    if (right != null && !right.errored) return null;
    recoverState();
    return null;
  }


  // =================================== READING A FULL PROGRAM ===================================

  /**
   * program ::= ( declaration | rule )*
   */
  private TRS readFullProgram(int kind) {
    ArrayList<Rule> rules = new ArrayList<Rule>();
    while (!_status.peekNext().isEof()) {
      if (tryReadDeclaration()) continue;
      Rule rule = readRule();
      if (rule != null) rules.add(rule);
    }

    Alphabet alf = _symbols.queryCurrentAlphabet();
    try {
      if (kind == MSTRS) return TRSFactory.createMSTRS(alf, rules);
      if (kind == STRS) return TRSFactory.createApplicativeTRS(alf, rules);
      if (kind == CFS) return TRSFactory.createCFS(alf, rules, false);
      return TRSFactory.createAMS(_symbols.queryCurrentAlphabet(), rules, false);
    }
    catch (IllegalRuleError e) {
      _status.storeError(e.queryProblem(), null);
    }
    catch (IllegalSymbolError e) {
      _status.storeError(e.queryProblem(), null);
    }
    return null;
  }

  // ============================= HELPER FUNCTIONALITY FOR UNIT TESTS ============================

  static Type readTypeForUnitTest(ParsingStatus ps) {
    CoraInputReader reader = new CoraInputReader(ps);
    return reader.readType();
  }
  
  /** Data (the signature to use) and Type (the expected type of this term) may be null. */
  static Term readTermForUnitTest(ParsingStatus ps, SymbolData data, Type type) {
    CoraInputReader reader = new CoraInputReader(ps);
    if (data != null) reader._symbols = data;
    TermStructure structure = reader.readTermStructure();
    if (structure == null || structure.errored) return null;
    return reader.makeTerm(structure, type, true);
  }

  /** Symbol declaration */
  static boolean readDeclarationForUnitTest(ParsingStatus ps, SymbolData data) {
    CoraInputReader reader = new CoraInputReader(ps);
    if (data != null) reader._symbols = data;
    return reader.tryReadDeclaration();
  }

  /** Reading rules */
  static Rule readRuleForUnitTest(ParsingStatus ps, SymbolData data) {
    CoraInputReader reader = new CoraInputReader(ps);
    if (data != null) reader._symbols = data;
    return reader.readRule();
  }

  // ================================= FUNCTIONS FOR INTERNAL USE =================================

  /**
   * Reads the given type from string.
   * If constrainedTRS is set to true, then Int, Bool and String are recognised as pre-defined
   * sorts, and identifiers are restricted as they are when reading a constrained TRS (e.g., sort
   * names may not contain "+").  If it is set to false, then identifiers are more general and
   * the pre-defined types will not be marked as theory sorts.
   */
  public static Type readTypeFromString(String str, boolean constrainedTRS) {
    ParsingStatus status =
      constrainedTRS ? new ParsingStatus(CoraTokenData.getConstrainedStringLexer(str), 10)
                     : new ParsingStatus(CoraTokenData.getUnconstrainedStringLexer(str), 10);
    CoraInputReader reader = new CoraInputReader(status);
    Type ret = reader.readType();
    Token token = status.nextToken();
    if (!token.isEof()) status.storeError("String continues after type has ended.", token);
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Reads the given type from string, recognising the pre-defined sorts.
   * This is the same as readTypeFromString(true).
   */
  public static Type readTypeFromString(String str) {
    return readTypeFromString(str, true);
  }

  /** Reads the given term from string */
  public static Term readTermFromString(String str, TRS trs) {
    ParsingStatus status;
    if (trs.isConstrained()) {
      status = new ParsingStatus(CoraTokenData.getConstrainedStringLexer(str), 10);
    }
    else status = new ParsingStatus(CoraTokenData.getUnconstrainedStringLexer(str), 10);
    CoraInputReader reader = new CoraInputReader(status, trs);
    TermStructure structure = reader.readTermStructure();
    Term ret = null;
    if (structure != null && !structure.errored) ret = reader.makeTerm(structure, null, true);
    Token token = status.nextToken();
    if (!token.isEof()) status.storeError("String continues after term has ended.", token);
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Parses the given program, and returns the TRS that it defines.
   * Here "kind" should be the kind of TRS (one of the constants defined at the head of the class).
   */
  public static TRS readProgramFromString(String str, int kind) {
    boolean constrained = kind == DEFAULT || kind == LCTRS;
    TokenQueue tq = constrained ? CoraTokenData.getConstrainedStringLexer(str)
                                : CoraTokenData.getUnconstrainedStringLexer(str);
    ParsingStatus status = new ParsingStatus(tq, 10);
    CoraInputReader reader = new CoraInputReader(status);
    TRS ret = reader.readFullProgram(kind);
    status.throwCollectedErrors();
    return ret;
  }

  /**
   * Parses the given program, and returns the TRS that it defines.  This assumes the input is
   * the most permissive format currently supported.
   */
  public static TRS readProgramFromString(String str) {
    return readProgramFromString(str, DEFAULT);
  }

  /** Reads the given file, parses the program in it, and returns the TRS that it defines. */
  public static TRS readProgramFromFile(String filename) throws IOException {
    int kind = DEFAULT;
    String extension =
      filename.substring(filename.lastIndexOf(".") + 1, filename.length()).toLowerCase();
    if (extension.equals("trs") || extension.equals("mstrs")) kind = MSTRS;
    if (extension.equals("lctrs")) kind = LCTRS;
    else if (extension.equals("atrs") || extension.equals("strs")) kind = STRS;
    else if (extension.equals("cfs") || extension.equals("afs")) kind = CFS;
    else if (extension.equals("ams") || extension.equals("afsm")) kind = AMS;
    boolean constrained = kind == DEFAULT || kind == LCTRS;

    TokenQueue tq = constrained ? CoraTokenData.getConstrainedFileLexer(filename)
                              : CoraTokenData.getUnconstrainedFileLexer(filename);
    ParsingStatus status = new ParsingStatus(tq, 10);
    CoraInputReader reader = new CoraInputReader(status);
    TRS ret = reader.readFullProgram(kind);
    status.throwCollectedErrors();
    return ret;
  }
}

