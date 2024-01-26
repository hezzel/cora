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

package cora.parser;

import com.google.common.collect.ImmutableList;
import java.util.TreeSet;

import cora.types.Type;
import cora.utils.LookupMap;
import cora.parser.lib.Token;

/**
 * This is not a real class, but rather a collection of the various data types that all parsers are
 * expected to parse and return.  It is done in this way to avoid having a dozen different files
 * which all just define a tiny data type.
 *
 * (The various parsers do have similar functionality such as a "readTerm" function, but it makes no
 * sense for them to have a shared inherit or interface because this functionality is static.)
 */
public interface Parser {
  /**
   * ParserTerm ::= Identifier(token, name)
   *              | Lambda(token, varname, type, arg) -- where type may be null (if not given)
   *              | Meta(token, name, args)           -- where args may be empty
   *              | Application(token, head, args)    -- where args may be empty
   *              | Tup(token, args)                  -- where args has length ≥ 1
   *              | BoolVal(token, istrue)            -- for TRUE or FALSE
   *              | IntVal(token, value)              -- for a (possibly negative) integer value
   *              | StringVal(token, escapedvalue)    -- for a string value (so in quotes)
   *              | CalcSymbol(token, name)           -- for a calculation symbol
   *              | PErr(ParserTerm)                  -- to indicate an error has occurred
   * This is a data type without dedicated functionality; only a toString() function for debugging,
   * and a function to check if there's an error anywhere inside the term.
   */
  public sealed interface ParserTerm permits Identifier, Lambda, Meta, Application, Tup,
                                             BoolVal, IntVal, StringVal, CalcSymbol, PErr {
    /** Indicates whether any errors occurred while parser this term (e.g., missing commas) */
    boolean hasErrors();
    Token token();
  }
  public record Identifier(Token token, String name) implements ParserTerm {
    public String toString() { return name; }
    public boolean hasErrors() { return false; }
  }
  public record Lambda(Token token, String vname, Type type, ParserTerm arg) implements ParserTerm {
    public String toString() {
      return "λ" + vname + (type == null ? "" : "::" + type.toString()) + "." + arg.toString();
    }
    public boolean hasErrors() { return arg.hasErrors(); }
  }
  public record Meta(Token token, String name,
                     ImmutableList<ParserTerm> args) implements ParserTerm {
    public String toString() { return name.toString() + "⟨" + args.toString() + "⟩"; }
    public boolean hasErrors() { return args.stream().anyMatch(ParserTerm::hasErrors); }
  }
  public record Application(Token token, ParserTerm head,
                            ImmutableList<ParserTerm> args) implements ParserTerm {
    public String toString() { return "@(" + head.toString() + ", " + args.toString() + ")"; }
    public boolean hasErrors() {
      return head.hasErrors() || args.stream().anyMatch(ParserTerm::hasErrors);
    }
  }
  public record Tup(Token token, ImmutableList<ParserTerm> args) implements ParserTerm {
    public String toString() { return "⦇" + args.toString() + "⦈"; }
    public boolean hasErrors() { return args.stream().anyMatch(ParserTerm::hasErrors); }
  }
  public record BoolVal(Token token, boolean istrue) implements ParserTerm {
    public String toString() { return istrue ? "⊤" : "⊥"; }
    public boolean hasErrors() { return false; }
  }
  public record IntVal(Token token, int value) implements ParserTerm {
    public String toString() { return "" + value; }
    public boolean hasErrors() { return false; }
  }
  public record StringVal(Token token, String escapedvalue) implements ParserTerm {
    public String toString() { return "" + escapedvalue; }
    public boolean hasErrors() { return false; }
  }
  public record CalcSymbol(Token token, String name) implements ParserTerm {
    public String toString() { return name; }
    public boolean hasErrors() { return false; }
  }
  public record PErr(ParserTerm t) implements ParserTerm {
    public String toString() { return "ERR(" + t.toString() + ")"; }
    public boolean hasErrors() { return true; }
    public Token token() { return t.token(); }
  }

  /**
   * ParserDeclaration ::= (token, name, type, extra).
   * This record is used for a function or variable declaration.  The extra field can be used in
   * two ways:
   * - for META-VARIABLE declarations, it is the arity; hence, for VARIABLE declarations it is
   *   necessarily 0
   * - for FUNCTION SYMBOL declarations, it indicates private status: 0 for public, 1 for private
   */
  public record ParserDeclaration(Token token, String name, Type type, int extra) {
    public ParserDeclaration(Token token, String name, Type type) {
      this(token, name, type, 0);
    }
  }

  /**
   * ParserRule ::= (token, vardecs, left, right, constraint)
   * This is a data type without dedicated functionality; only a toString() function for debugging.
   * The constraint is not used in all formalisms, and may be null.
   */
  public record ParserRule(Token token, LookupMap<ParserDeclaration> vars, ParserTerm left,
                           ParserTerm right, ParserTerm constraint) {
    public ParserRule(Token token, LookupMap<ParserDeclaration> vars, ParserTerm left,
                      ParserTerm right) {
      this(token, vars, left, right, null);
    }
    public boolean hasErrors() {
      return left.hasErrors() || right.hasErrors() || (constraint != null && constraint.hasErrors());
    }
    public String toString() {
      return "{ " + vars.keySet().toString() + " } " + left.toString() + " → " + right.toString() +
        (constraint == null ? "" : " | " + constraint.toString());
    }
  }

  /**
   * A "program" essentially defines TRS, except it is not yet typed.  It consists of a number of
   * function symbol declarations, a number of rules, and a set of "private" symbols (all others
   * are public).
   */
  public record ParserProgram(LookupMap<ParserDeclaration> fundecs,
                              ImmutableList<ParserRule> rules) {}
}

