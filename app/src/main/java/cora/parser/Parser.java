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
import cora.types.Type;
import cora.utils.LookupMap;
import cora.parser.lib.Token;

/**
 * This interface defines the various data types that all the parsers are expected to parse and
 * return.
 */
public interface Parser {
  /*
   * Not defined in this interface because they are static, but for convenient and consistent
   * usage, all implementations of Parser are expected to provide the following static methods:
   *
   * // reads a term from a string, storing parse errors into the collecotr
   * static ParserTerm readTerm(String str, ErrorCollector collector)
   * // reads a rule from a string, storing parse errors into the collector
   * static ParserRule readRule(String str)
   * // reads a set of (function or variable) declarations
   * static LookupMap<ParserDeclaration> readDeclarations(String str, ErrorCollector collector)
   * // reads a full TRS from string, storing parse errors into the collector
   * static ParserProgram readProgramFromString(String str, ErrorCollector collector)
   * // reads a full TRS from file, storing parse errors into the collector
   * // and throwing an IOException if there are problems reading the file
   * static ParserProgram readProgramFromFile(String str, ErrorCollector collector) throws IOException
   *
   * All the above functions use the format expected for the current parser.
   *
   * If errors occur while parsing but we can reasonably try to recover from them, then they are
   * merely stored in the error collector.  However, if we should not attempt further recovery,
   * then a cora.exceptions.ParseError is thrown instead.
   *
   * For all these functions, there should also be a version which omits the ErrorCollector.  Using
   * this version implies that errors should be thrown before the function returns.
   */

  /**
   * ParserTerm ::= Identifier(token, name)
   *              | Lambda(token, varname, type, arg)
   *              | Meta(token, name, args)           -- where args may be empty
   *              | Application(token, head, args)    -- where args may be empty
   *              | Tuple(token, args)                -- where args has length ≥ 1
   *              | PErr(ParserTerm)                  -- to indicate an error has occurred
   * This is a data type without dedicated functionality; only a toString() function for debugging,
   * and a function to check if there's an error anywhere inside the term.
   */
  public sealed interface ParserTerm permits Identifier, Lambda, Meta, Application, Tuple, PErr {
    /** Indicates whether any errors occurred while parser this term (e.g., missing commas) */
    boolean hasErrors();
  }
  public record Identifier(Token token, String name) implements ParserTerm {
    public String toString() { return name; }
    public boolean hasErrors() { return false; }
  }
  public record Lambda(Token t, String varname, Type type, ParserTerm arg) implements ParserTerm {
    public String toString() {
      return "λ" + varname + "::" + type.toString() + "." + arg.toString();
    }
    public boolean hasErrors() { return arg.hasErrors(); }
  }
  public record Meta(Token t, String name, ImmutableList<ParserTerm> args) implements ParserTerm {
    public String toString() { return name.toString() + "⟨" + args.toString() + "⟩"; }
    public boolean hasErrors() { return args.stream().anyMatch(ParserTerm::hasErrors); }
  }
  public record Application(Token t, ParserTerm head,
                            ImmutableList<ParserTerm> args) implements ParserTerm {
    public String toString() { return "@(" + head.toString() + ", " + args.toString() + ")"; }
    public boolean hasErrors() {
      return head.hasErrors() || args.stream().anyMatch(ParserTerm::hasErrors);
    }
  }
  public record Tuple(Token t, ImmutableList<ParserTerm> args) implements ParserTerm {
    public String toString() { return "⦇" + args.toString() + "⦈"; }
    public boolean hasErrors() { return args.stream().anyMatch(ParserTerm::hasErrors); }
  }
  public record PErr(ParserTerm t) implements ParserTerm {
    public String toString() { return "ERR(" + t.toString() + ")"; }
    public boolean hasErrors() { return true; }
  }

  /**
   * ParserDeclaration ::= (token, name, type).
   * This record is used for a function or variable declaration.
   */
  public record ParserDeclaration(Token token, String name, Type type) {}

  /**
   * ParserRule ::= BasicRule(token, vardecs, left, right)
   *              | ConstrainedRule(token, vardecs, left, right, constraint)
   * This is a data type without dedicated functionality; only a toString() function for debugging.
   */
  public sealed interface ParserRule permits BasicRule, ConstrainedRule {
    boolean hasErrors();
    Token token();
    LookupMap<ParserDeclaration> vars();
    ParserTerm left();
    ParserTerm right();
    ParserTerm constraint();
  }
  public record BasicRule(Token token, LookupMap<ParserDeclaration> vars,
                          ParserTerm left, ParserTerm right) implements ParserRule {
    public String toString() {
      return "{ " + vars.keySet().toString() + " } " + left.toString() + " → " + right.toString();
    }
    public boolean hasErrors() { return left.hasErrors() || right.hasErrors(); }
    public ParserTerm constraint() { return null; }
  }
  public record ConstrainedRule(Token token, LookupMap<ParserDeclaration> vars,
                  ParserTerm left, ParserTerm right, ParserTerm constraint) implements ParserRule {
    public String toString() {
      return "{ " + vars.keySet().toString() + " } " + left.toString() + " → " + right.toString() +
             " | " + constraint.toString();
    }
    public boolean hasErrors() { return left.hasErrors() || right.hasErrors(); }
  }

  /**
   * A "program" essentially defines TRS, except it is not yet typed.  It consists of a number of
   * function symbol declarations, and a number of rules.
   */
  public record ParserProgram(LookupMap<ParserDeclaration> fundecs,
                              ImmutableList<ParserRule> rules) {}
}

