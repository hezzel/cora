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

package charlie.parser;

import com.google.common.collect.ImmutableList;
import java.io.IOException;
import java.util.ArrayList;

import charlie.util.LookupMap;
import charlie.types.*;
import charlie.parser.lib.*;
import charlie.parser.InfixManager.OperatorData;
import charlie.parser.Parser.*;

/**
 * The CoraParser parses the main Cora input format -- both for the unconstrained basic formalisms
 * (which do not have any theory symbols), and the constrained ones (which currently include all
 * the standard formalisms).
 */
public class CoraParser {
  public static final String PLUS = "+";
  public static final String MINUS = "-";
  public static final String TIMES = "*";
  public static final String DIV = "/";
  public static final String MOD = "%";
  public static final String GREATER = ">";
  public static final String SMALLER = "<";
  public static final String GEQ = "≥";
  public static final String LEQ = "≤";
  public static final String EQUALS = "=";
  public static final String NEQ = "≠";
  public static final String AND = "∧";
  public static final String OR = "∨";
  public static final String NOT = "¬";

  /**
   * The parser keeps track of the status of parser so far; all read functions have a (potential)
   * side effect of advancing the parsing status.
   */
  private ParsingStatus _status;

  /** This infix manager is used for parsing (sub-)terms with infix operators. */
  private InfixManager _manager;

  /**
   * Stores the parsing status for use by methods of the CoraParser class.
   * Private because the CoraParser should only be created by the static methods in the class.
   */
  private CoraParser(ParsingStatus status) {
    _status = status;
    _manager = new InfixManager();
    _manager.addGroup(InfixManager.ASSOC_LEFT, 1, AND);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 1, OR);
    _manager.addGroup(InfixManager.ASSOC_NONE, 2, EQUALS, NEQ, GREATER, SMALLER, GEQ, LEQ);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 3, PLUS, MINUS);
    _manager.addGroup(InfixManager.ASSOC_LEFT, 4, TIMES, DIV, MOD);
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
   * type ::= basictype (typearrow type)?
   *
   * This function reads a type and returns it.
   * The input is expected to actually be a type. If this is not the case, then an error is stored.
   * If some kind of error recovery could be done, a Type is still returned; otherwise, null may be
   * returned, even if something was read -- indicating that we will have to do large-scale error
   * recovery.
   */
  private Type readType() {
    Type start = readBasicType();
    if (_status.readNextIf(CoraTokenData.ARROW) == null) return start;
    Type end = readType();
    if (start != null && end != null) return TypeFactory.createArrow(start, end);
    // error recovery
    if (start == null) return end;
    return start;
  }

  /**
   * basictype ::= sort
   *             | producttype
   *             | BRACKETOPEN type BRACKETCLOSE
   *
   * where
   * sort ::= INTTYPE | BOOLTYPE | STRINGTYPE | IDENTIFIER
   *
   * This function reads a basic type and returns it.  The input is expected to actually start with
   * a basic type.  If this is not the case, then an error is stored and either null is returned, or
   * whatever type we did manage to read.
   */
  private Type readBasicType() {
    if (_status.readNextIf(CoraTokenData.INTTYPE) != null) return TypeFactory.intSort;
    if (_status.readNextIf(CoraTokenData.BOOLTYPE) != null) return TypeFactory.boolSort;
    if (_status.readNextIf(CoraTokenData.STRINGTYPE) != null) return TypeFactory.stringSort;
    String name = tryReadIdentifier();
    if (name != null) return TypeFactory.createSort(name);
    if (_status.nextTokenIs(CoraTokenData.TUPLEOPEN)) return readProductType();
    Token bracket = _status.expect(CoraTokenData.BRACKETOPEN,
      "a type (started by a sort identifier or bracket)");
    if (bracket == null) return null;
    Type ret = readType();
    _status.expect(CoraTokenData.BRACKETCLOSE, "closing bracket");
    return ret;
  }

  /**
   * producttype ::= TUPLEOPEN basictype COMMA...COMMA basictype TUPLECLOSE
   * 
   * This function reads a product type and returns it.  The input is expected to actually start
   * with a product type.  If this is not the case, then an error is stored and either null is
   * returned, or whatever type we did manage to read. (We try to complete the product, with a
   * normal closing bracket rather than a tuple closing bracket if we have to).
   */
  private Type readProductType() {
    _status.expect(CoraTokenData.TUPLEOPEN, "tuple opening bracket");
    ArrayList<Type> components = new ArrayList<Type>();
    Type arg = readType();
    while (_status.readNextIf(CoraTokenData.COMMA) != null) {
      if (arg != null) components.add(arg);
      arg = readType();
    }
    if (arg != null) components.add(arg);
    if (_status.expect(CoraTokenData.TUPLECLOSE, "tuple closing bracket") == null) {
      _status.readNextIf(CoraTokenData.BRACKETCLOSE);
    }
    if (components.size() == 0) return null;
    if (components.size() == 1) return components.get(0);
    return TypeFactory.createProduct(components);
  }

  // ======================================== READING TERMS =======================================

  /**
   * term = abstraction
   *      | mainterm (infixsymbol mainterm)*
   *
   * When the current parsing status represents a term, this method reads it into a ParserTerm.
   * This function expects to read a term; if it fails, error recovery is attempted to still return
   * a term, but if that fails altogether, null is returned.  It is possible, but not guaranteed,
   * that symbols were still read if null is returned.
   */
  private  ParserTerm readTerm() {
    if (_status.nextTokenIs(CoraTokenData.LAMBDA)) return readAbstraction();
    ParserTerm ret = readMainTerm();
    if (ret == null) return null;

    OperatorData operator = tryReadInfixSymbol();
    if (operator == null) return ret;
    ArrayList<ParserTerm> parts = new ArrayList<ParserTerm>();
    ArrayList<OperatorData> ops = new ArrayList<OperatorData>();
    parts.add(ret);

    boolean errored = false;
    while (operator != null) {
      ops.add(operator);
      ParserTerm pt = readMainTerm();
      if (pt == null) { errored = true; ops.remove(ops.size()-1); break; }
      parts.add(pt);
      operator = tryReadInfixSymbol();
    }   
    ret = _manager.convertChain(parts, ops, _status);
    if (errored) ret = new PErr(ret);
    return ret;
  }

  /**
   * mainterm = value
   *          | IDENTIFIER
   *          | IDENTIFIER METAOPEN termlist METACLOSE
   *          | mainterm BRACKETOPEN termlist BRACKETCLOSE
   *          | BRACKETOPEN term BRACKETCLOSE
   *          | TUPLEOPEN termlist TUPLECLOSE
   *          | METAOPEN infixsymbol METACLOSE
   *          | NOT mainterm
   *          | MINUS mainterm
   */
  private ParserTerm readMainTerm() {
    ParserTerm ret = null;
    Token token;

    // NOT mainterm
    if ((token =_status.readNextIf(CoraTokenData.NOT)) != null) {
      ParserTerm child = readMainTerm();
      if (child == null) return new CalcSymbol(token, NOT);
      return new Application(token, new CalcSymbol(token, NOT), ImmutableList.of(child));
    }

    // MINUS mainterm
    if ((token = _status.readNextIf(CoraTokenData.MINUS)) != null) {
      ParserTerm child = readMainTerm();
      if (child == null) return new CalcSymbol(token, MINUS);
      if (child instanceof IntVal(Token t, int v)) return new IntVal(token, -v);
      return new Application(token, new CalcSymbol(token, MINUS), ImmutableList.of(child));
    }

    // value
    if (_status.nextTokenIs(CoraTokenData.STRING) ||
        _status.nextTokenIs(CoraTokenData.INTEGER) ||
        _status.nextTokenIs(CoraTokenData.TRUE) ||
        _status.nextTokenIs(CoraTokenData.FALSE)) {
      ret = readValue();
    }

    // BRACKETOPEN term BRACKETCLOSE  -- we store term as ret
    else if (_status.readNextIf(CoraTokenData.BRACKETOPEN) != null) {
      ret = readTerm();
      if (ret == null) { _status.readNextIf(CoraTokenData.BRACKETCLOSE); return null; }
      if (_status.expect(CoraTokenData.BRACKETCLOSE, "a closing bracket") == null) {
        return new PErr(ret);
      }
    }

    // METAOPEN infixsymbol METACLOSE
    else if (_status.readNextIf(CoraTokenData.METAOPEN) != null) {
      token = _status.peekNext();
      OperatorData data = tryReadInfixSymbol();
      if (data == null && _status.readNextIf(CoraTokenData.NOT) != null) {
        data = new OperatorData(token, NOT);
      }
      if (data == null) {
        _status.storeError("Expected infix symbol but got " + token.getName() + " (" +
          token.getText() + ")", token);
        ret = new PErr(new Identifier(token, token.getText()));
        _status.nextToken();
      }
      else {
        ret = new CalcSymbol(data.token(), data.name());
      }
      Token end = _status.expect(CoraTokenData.METACLOSE, "infix closing bracket ]");
      if (end == null) return new PErr(ret);
    }

    // TUPLEOPEN termlist TUPLECLOSE
    else if ((token = _status.readNextIf(CoraTokenData.TUPLEOPEN)) != null) {
      ImmutableList<ParserTerm> args =
        readTermList(CoraTokenData.TUPLECLOSE, "tuple closing bracket ⦈");
      if (args == null || args.size() == 0) {
        ret = new PErr(new Identifier(token, "⦇⦈"));
        if (args != null) _status.storeError("Empty tuples are not allowed.", token);
      }
      else if (args.size() == 1) {
        _status.storeError("Tuples of length 1 are not allowed.", token);
        ret = args.get(0);
      }
      else ret = new Tup(token, args);
    }

    // IDENTIFIER
    else {
      token = _status.expect(CoraTokenData.IDENTIFIER, "term, started by an identifier, " +
        "λ, string or (,");
      if (token == null) return null;
      Token next;
      // IDENTIFIER METAOPEN termlist METACLOSE
      if ((next = _status.readNextIf(CoraTokenData.METAOPEN)) != null) {
        ImmutableList args = readTermList(CoraTokenData.METACLOSE, "meta-closing bracket " +
          (next.getText().equals("[") ? "]" : "⟩"));
        if (args == null) ret = new PErr(new Meta(token, token.getText(), ImmutableList.of()));
        else ret = new Meta(token, token.getText(), args);
      }
      // just IDENTIFIER (so a function symbol or variable)
      else ret = new Identifier(token, token.getText());
    }

    // if we see an argument list, read it, and make the application structure
    while (_status.readNextIf(CoraTokenData.BRACKETOPEN) != null) {
      ImmutableList args = readTermList(CoraTokenData.BRACKETCLOSE, "closing bracket )");
      if (args == null) ret = new PErr(ret);
      else ret = new Application(ret.token(), ret, args);
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
  private ParserTerm readAbstraction() {
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
    ParserTerm ret = readTerm();
    if (ret == null) return null;

    // put everything together
    for (int i = variables.size()-1; i >= 0; i--) {
      ret = new Lambda(tokens.get(i), variables.get(i), types.get(i), ret);
    }
    if (errored) ret = new PErr(ret);
    return ret;
  }

  /**
   * value = STRING+ | INT | TRUE | FALSE
   *
   * This function is really only called when we already know the next token is a string, int, or
   * boolean constant, so should not fail.  In the case of strings, it eagerly reads as many
   * strings as are available.
   */
  private ParserTerm readValue() {
    Token token = _status.nextToken();
    if (token.getName().equals(CoraTokenData.TRUE)) return new BoolVal(token, true);
    if (token.getName().equals(CoraTokenData.FALSE)) return new BoolVal(token, false);
    if (token.getName().equals(CoraTokenData.INTEGER)) {
      try {
        int number = Integer.parseInt(token.getText());
        return new IntVal(token, number);
      }
      catch (NumberFormatException e) {
        _status.storeError("Cannot parse integer constant: " + token.getText(), token);
        return new Identifier(token, token.getText());
      }
    }
    if (!token.getName().equals(CoraTokenData.STRING)) {
      throw new Error("Calling readValueStructure when it shouldn't be.");
    }
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
    return new StringVal(token, text.toString());
  }

  /**
   * termlist ::= ε [followName] | term (COMMA term)* [followName]
   *
   * The terms are returned as an ImmutableList.
   */
  private ImmutableList<ParserTerm> readTermList(String followName, String followDescription) {
    // handle the case ε [followName]
    if (_status.readNextIf(followName) != null) return ImmutableList.of();

    Token token;
    ArrayList<ParserTerm> ret = new ArrayList<ParserTerm>();
    boolean errored = false;    // keep track of if we should mark the next term as an error

    // read the arguments until we encounter [followName] or we're in an overly weird place
    while (true) {
      // appropriate error handling if we see commas where there shouldn't be
      if ((token = _status.readNextIf(CoraTokenData.COMMA)) != null) {
        _status.storeError("Unexpected comma; expected term or " + followDescription, token);
        errored = true;
        while (_status.readNextIf(CoraTokenData.COMMA) != null);
      }
      // read the next term in the list
      ParserTerm arg = readTerm();
      if (arg == null) errored = true;
      else {
        if (errored) { arg = new PErr(arg); errored = false; }
        ret.add(arg);
      }
      if (_status.readNextIf(followName) != null) break;
      if (_status.expect(CoraTokenData.COMMA, "a comma or " + followDescription) == null) {
        // we recover from a missing comma, but only if we're still followed by another term
        errored = true;
        if (!nextMayBeTerm()) break;
      }
    }
    if (errored) {
      if (ret.size() == 0) return null;
      ret.set(ret.size()-1, new PErr(ret.get(ret.size()-1)));
    }
    return ImmutableList.copyOf(ret);
  }

  /**
   * If the next token is an infix operator, this function reads it and returns the corresponding
   * OperatorData.  If not, nothing is read and null is returned.
   */
  private OperatorData tryReadInfixSymbol() {
    Token token = _status.peekNext();
    if (_status.readNextIf(CoraTokenData.PLUS) != null)    return new OperatorData(token, PLUS);
    if (_status.readNextIf(CoraTokenData.MINUS) != null)   return new OperatorData(token, MINUS);
    if (_status.readNextIf(CoraTokenData.TIMES) != null)   return new OperatorData(token, TIMES);
    if (_status.readNextIf(CoraTokenData.DIV) != null)     return new OperatorData(token, DIV);
    if (_status.readNextIf(CoraTokenData.MOD) != null)     return new OperatorData(token, MOD);
    if (_status.readNextIf(CoraTokenData.AND) != null)     return new OperatorData(token, AND);
    if (_status.readNextIf(CoraTokenData.OR) != null)      return new OperatorData(token, OR);
    if (_status.readNextIf(CoraTokenData.GREATER) != null) return new OperatorData(token, GREATER);
    if (_status.readNextIf(CoraTokenData.SMALLER) != null) return new OperatorData(token, SMALLER);
    if (_status.readNextIf(CoraTokenData.GEQ) != null)     return new OperatorData(token, GEQ);
    if (_status.readNextIf(CoraTokenData.LEQ) != null)     return new OperatorData(token, LEQ);
    if (_status.readNextIf(CoraTokenData.EQUAL) != null)   return new OperatorData(token, EQUALS);
    if (_status.readNextIf(CoraTokenData.UNEQUAL) != null) return new OperatorData(token, NEQ);
    return null;
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
           _status.nextTokenIs(CoraTokenData.METAOPEN) ||
           _status.nextTokenIs(CoraTokenData.IDENTIFIER);
  }

  // ======================================== READING RULES =======================================

  /** 
   * environment ::= BRACEOPEN BRACECLOSE
   *               | BRACEOPEN mdeclaration (COMMA mdeclaration)* BRACECLOSE
   *
   * This always returns a lookup map, even if errors occur (although it may be empty).
   */
  private LookupMap<ParserDeclaration> readEnvironment() {
    LookupMap.Builder<ParserDeclaration> ret = new LookupMap.Builder<ParserDeclaration>();
    if (_status.expect(CoraTokenData.BRACEOPEN, "environment opening brace {") == null) {
      return ret.build();
    }
    if (_status.readNextIf(CoraTokenData.BRACECLOSE) != null) return ret.build();  // { }
    while (true) {
      ParserDeclaration decl = readMetaVariableDeclaration();
      if (decl != null) {
        String name = decl.name();
        if (ret.containsKey(name)) {
          String kind = decl.extra() == 0 ? "variable" : "meta-variable";
          _status.storeError("Redeclaration of " + (decl.extra() == 0 ? "variable " :
           "meta-variable ") + name + " in the same environment.", decl.token());
        }
        else ret.put(decl.name(), decl);
      }
      if (_status.readNextIf(CoraTokenData.BRACECLOSE) != null) return ret.build();
      if (_status.expect(CoraTokenData.COMMA, "comma or }") == null) {
        if (!readRecoverEnvironment().getName().equals(CoraTokenData.COMMA)) return ret.build();
      }
    }
  }

  /**
   * mdeclaration ::= IDENTIFIER DECLARE type
   *                | IDENTIFIER DECLARE METAOPEN METACLOSE typearrow type
   *                | IDENTIFIER DECLARE METAOPEN type (COMMA type)* METACLOSE typearrow type
   *
   * This may return null if no valid declaration was given (in which case an error is stored).
   */
  private ParserDeclaration readMetaVariableDeclaration() {
    Token token = _status.expect(CoraTokenData.IDENTIFIER, "a variable or meta-variable name");
    Token decl = _status.expect(CoraTokenData.DECLARE, "declare symbol (::)");
    if (token == null && decl == null) return null;

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
            if (type == null) return null; // no idea where we are now, probably try recovery
          }
        }
      }
      _status.expect(CoraTokenData.ARROW, "arrow operator →");
    }
    else _status.readNextIf(CoraTokenData.ARROW);

    Type type = readType();
    if (type == null) return null;
    
    for (int i = args.size()-1; i >= 0; i--) {
      type = TypeFactory.createArrow(args.get(i), type);
    }
    return new ParserDeclaration(token, token.getText(), type, args.size());
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

  /**  
   * rule ::= environment? term ARROW term (MID term)?
   *
   * If reading a ParserRule fails, we immediately do error recovery, to return to a state where
   * the next rule or declaraiton can be read.
   */
  private ParserRule readRule() {
    Token start = _status.peekNext();
    LookupMap<ParserDeclaration> vars = null;
    if (_status.nextTokenIs(CoraTokenData.BRACEOPEN)) vars = readEnvironment();
    else vars = LookupMap.<ParserDeclaration>empty();
    // this could happen due to error recovery, but means we should stop trying to read this rule
    if (_status.nextTokenIs(CoraTokenData.BRACEOPEN)) return null;
    ParserTerm left = readTerm();
    boolean ok = _status.expect(CoraTokenData.ARROW, "an arrow (→ or ->)") != null;
    ParserTerm right = ok ? readTerm() : null;
    ParserTerm constraint = null;
    if (_status.readNextIf(CoraTokenData.MID) != null) constraint = readTerm();
    if (left != null && right != null) return new ParserRule(start, vars, left, right, constraint);
    // error recovery: something went wrong reading the terms
    if (right == null || right.hasErrors() || (constraint != null && constraint.hasErrors())) {
      recoverState();
    }
    return null;
  }
 
  // ====================================== READING FULL TRSs =====================================

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
      // } <-- we're past the rule declaration part, but still at the start of a rule; we're
      // probably going to run into typing trouble, but so be it
      if (curr.getName().equals(CoraTokenData.BRACECLOSE)) { _status.pushBack(curr); return; }
      // public / private <-- we're at the start of a function symbol declaration
      if (curr.getName().equals(CoraTokenData.PUBLIC) ||
          curr.getName().equals(CoraTokenData.PRIVATE)) { _status.pushBack(curr); return; }
      // | <-- we're at the constraint part of a rule, so we can continue after reading the
      // constraint
      if (curr.getName().equals(CoraTokenData.MID)) {
        ParserTerm term = readTerm();
        if (term != null && !term.hasErrors()) return;
      }
      // :: <-- we may be a token into a declaration; it is also possible that we are inside an
      // environment or abstraction (although unlikely as we try to account for that possiblity)
      // but if the next step is to read a function symbol, this step will fail anyway if it is
      // actually a variable or meta-variable declaration
      if (curr.getName().equals(CoraTokenData.DECLARE) && prev != null &&
          prev.getName().equals(CoraTokenData.IDENTIFIER)) {
        _status.pushBack(curr);
        _status.pushBack(prev);
        return;
      }
      // we're following a declare, so we can definitely be inside a type, no matter what came
      // before!
      if (curr.getName().equals(CoraTokenData.DECLARE)) intype = true;
      // ( or [ <-- if this comes directly after an identifier, we are not in a type
      if ((curr.getName().equals(CoraTokenData.BRACKETOPEN) ||
           curr.getName().equals(CoraTokenData.METAOPEN)) &&
          prev != null && prev.getName().equals(CoraTokenData.IDENTIFIER)) {
        intype = false;
      }
      // . <-- we're after a lambda declaration, so no longer in a type at least
      if (curr.getName().equals(CoraTokenData.DOT)) intype = false;
      // → when we're not in a type <-- we're before the right-hand side of a rule
      if (curr.getName().equals(CoraTokenData.ARROW) && !intype) {
        ParserTerm t = readTerm();
        if (t != null) {
          if (_status.readNextIf(CoraTokenData.MID) != null) t = readTerm();
        }
        if (t != null && !t.hasErrors()) return;
      }
    }
  }

  /**
   * fundec ::= (PUBLIC|PRIVATE)? IDENTIFIER DECLARE type
   * fundecs are never followed by DOT or COMMA.
   *
   * There are three possible return values:
   * - null: nothing was read; this is not a declaration
   *   (this occurs if the upcoming token is neither PUBLIC nor PRIVATE, nor are the upcoming two
   *   tokens IDENTIFIER DECLARE)
   * - a ParserDeclaration with type() null: this is not a valid declaration, and an error was
   *   stored, but at least one token has been read; in this case, error recovery is immediately
   *   done to ensure that the status is back to a program line.
   * - a valid ParserDeclaration
   */
  private ParserDeclaration tryReadDeclaration() {
    Token publ, priv, constant;

    publ = _status.readNextIf(CoraTokenData.PUBLIC);
    priv = (publ != null) ? null : _status.readNextIf(CoraTokenData.PRIVATE);

    // PUBLIC / PRIVATE: this *has* to be a parser declaration!
    if (publ != null || priv != null) {
      constant = _status.expect(CoraTokenData.IDENTIFIER,
        "an identifier (for a function symbol name to be declared)");
      Token declaresymb = _status.expect(CoraTokenData.DECLARE, "::");
      if (constant == null || declaresymb == null) {
        recoverState();
        return new ParserDeclaration(publ == null ? priv : publ, "public/private", null);
      }
    }
    else {
      constant = _status.readNextIf(CoraTokenData.IDENTIFIER);
      if (constant == null) return null;
      if (_status.readNextIf(CoraTokenData.DECLARE) == null) {
        _status.pushBack(constant);
        return null;
      }
    }
    Type type = readType();
    String name = constant.getText();

    // error cases: this is actually a variable / meta-variable declaration!
    if (_status.nextTokenIs(CoraTokenData.BRACECLOSE)) {
      if (publ != null || priv != null) {
        _status.storeError("Function symbol declartion cannot be followed by }!",
                           _status.peekNext());
      }
      return new ParserDeclaration(constant, name, null);
    }
    if (_status.nextTokenIs(CoraTokenData.COMMA) || _status.nextTokenIs(CoraTokenData.DOT) ||
        type == null) {
      if (publ != null || priv != null) {
        Token tok = _status.peekNext();
        _status.storeError("Function symbol declartion cannot be followed by " +
                           (tok.getName().equals(CoraTokenData.COMMA) ? "comma" : "dot") + "!",
                           _status.peekNext());
      }
      recoverState();
      return new ParserDeclaration(constant, name, null);
    }

    return new ParserDeclaration(constant, name, type, priv == null ? 0 : 1);
  }

  private ParserProgram readTRS() {
    LookupMap.Builder<ParserDeclaration> symbols = new LookupMap.Builder<ParserDeclaration>();
    ImmutableList.Builder<ParserRule> rules = ImmutableList.<ParserRule>builder();
    while (!_status.peekNext().isEof()) {
      ParserDeclaration decl = tryReadDeclaration();
      if (decl == null) {
        ParserRule rule = readRule();
        if (rule != null) rules.add(rule);
      }
      else if (decl.type() != null) {
        if (symbols.containsKey(decl.name())) {
          _status.storeError("Redeclaration of previously declared function symbol " + decl.name() +
            ".", decl.token());
        }
        else symbols.put(decl.name(), decl);
      }
    }
    return new ParserProgram(symbols.build(), rules.build());
  }

  // ====================================== PUBLIC FUNCTIONS ======================================

  /**
   * Helper function: creates a status to read the given string and store errors in the given
   * collector, which may be null (in which case errors are stored in a fresh collector in the
   * status).
   */
  private static ParsingStatus makeStatus(String str, boolean constrained,
                                          ErrorCollector collector) {
    if (collector == null) collector = new ErrorCollector();
    TokenQueue queue;
    if (constrained) queue = CoraTokenData.getConstrainedStringLexer(str);
    else queue = CoraTokenData.getUnconstrainedStringLexer(str);
    return new ParsingStatus(queue, collector);
  }

  /** Helper function to make sure we are done parsing, and have no errors */
  private static void finish(ParsingStatus status, boolean throwErrors) {
    status.expect(Token.EOF, "end of input");
    if (throwErrors) status.throwCollectedErrors();
  }

  /**  
   * Reads the given type from string.
   * If constrainedTRS is set to true, then Int, Bool and String are recognised as pre-defined
   * sorts, and identifiers are restricted as they are when reading a constrained TRS (e.g., sort
   * names may not contain "+").  If it is set to false, then identifiers are more general and
   * the pre-defined types will not be marked as theory sorts.
   * @throws charlie.exceptions.ParseException
   */
  public static Type readType(String str, boolean constrainedTRS, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrainedTRS, collector);
    CoraParser parser = new CoraParser(status);
    Type ret = parser.readType();
    finish(status, collector == null || ret == null);
    return ret; 
  }

  /**
   * Reads the given type from string, recognising the pre-defined sorts.
   * This is the same as readTypeFromString(true, null).
   */
   public static Type readType(String str) { return readType(str, true, null); }

  /**
   * Reads a term from the given string.
   * If constrainedTRS is set to true, then tokens for theories and constraints are recognised and
   * parsed accordingly; if not, these are just identifiers.
   * The error collector is allowed to be null.  If an error collector is given, then parsing tries
   * error recovery, and stores its erorrs in the given collector; only if parsing really fails is
   * an error thrown.  If the given collector is null, any error causes a ParseException to be
   * thrown (although we still try to collect all relevant errors in the same ParseException).
   * @throws charlie.exceptions.ParseException
   */
  public static ParserTerm readTerm(String str, boolean constrainedTRS, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrainedTRS, collector);
    CoraParser parser = new CoraParser(status);
    ParserTerm ret = parser.readTerm();
    finish(status, collector == null || ret == null);
    return ret;
  }

  /**
   * Reads a rule from the given string.
   * @throws charlie.exceptions.ParseException
   */
  public static ParserRule readRule(String str, boolean constrained, ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrained, collector);
    CoraParser parser = new CoraParser(status);
    ParserRule rule = parser.readRule();
    finish(status, collector == null || rule == null);
    return rule;
  }
  public static ParserRule readRule(String str) { return readRule(str, true, null); }

  /**
   * Reads a function declaration from the given string.
   * Since this is primarily meant for use in unit testing, the output can be one of the following
   * options:
   * - null: if nothing was read
   * - a ParserDeclaration with type() null: if something was read, but an error occurred
   * - a valid ParserDeclaration: if the declaration was read
   *   if the declaration is private, moreover the extra() field is 1; otherwise it is 0.
   * @throws charlie.exceptions.ParseException
   */
  public static ParserDeclaration readDeclaration(String str, boolean constrained,
                                                  ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrained, collector);
    CoraParser parser = new CoraParser(status);
    ParserDeclaration decl = parser.tryReadDeclaration();
    status.expect(Token.EOF, "end of input");
    return decl;
  }

  /**
   * Reads a full TRS from the given string, allowing theory symbols and constraints if and only
   * if constrained is set to true.
   */
  public static ParserProgram readProgramFromString(String str, boolean constrained,
                                                    ErrorCollector collector) {
    ParsingStatus status = makeStatus(str, constrained, collector);
    CoraParser parser = new CoraParser(status);
    ParserProgram program = parser.readTRS();
    finish(status, collector == null || program == null);
    return program;
  }
  public static ParserProgram readProgramFromString(String str) {
    return readProgramFromString(str, true, null);
  }

  /**
   * Reads a full TRS, in the expected format for the current parser, from the given file.
   * @throws charlie.exceptions.ParseException
   */
  public static ParserProgram readProgramFromFile(String filename, boolean constrained,
                                                  ErrorCollector collector) throws IOException {
    TokenQueue queue;
    if (constrained) queue = CoraTokenData.getConstrainedFileLexer(filename);
    else queue = CoraTokenData.getUnconstrainedFileLexer(filename);
    ParsingStatus status =
      new ParsingStatus(queue, collector == null ? new ErrorCollector() : collector);
    CoraParser parser = new CoraParser(status);
    ParserProgram program = parser.readTRS();
    finish(status, collector == null || program == null);
    return program;
  }

  /**
   * Reads a sequence of terms from a file, all in the expected Cora format.
   * @throws charlie.exceptions.ParseException
   */
  public static ArrayList<ParserTerm> readTermFromFile(String filename, boolean constrained,
                                               ErrorCollector collector) throws IOException {
    TokenQueue queue;
    if (constrained) queue = CoraTokenData.getConstrainedFileLexer(filename);
    else queue = CoraTokenData.getUnconstrainedFileLexer(filename);
    ParsingStatus status =
      new ParsingStatus(queue, collector == null ? new ErrorCollector() : collector);
    CoraParser parser = new CoraParser(status);
    ArrayList<ParserTerm> ret = new ArrayList<ParserTerm>();
    while (!status.peekNext().isEof()) {
      ParserTerm t = parser.readTerm();
      if (t != null) ret.add(t);
      if (collector == null || t == null) status.throwCollectedErrors();
    }
    return ret;
  }
}

