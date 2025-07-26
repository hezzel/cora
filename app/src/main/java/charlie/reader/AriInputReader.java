/**************************************************************************************************
 Copyright 2023--2025 Cynthia Kop

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

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;

import charlie.exceptions.*;
import charlie.util.FixedList;
import charlie.util.LookupMap;
import charlie.types.*;
import charlie.parser.lib.Token;
import charlie.parser.lib.ParsingException;
import charlie.parser.lib.ErrorCollector;
import charlie.parser.Parser;
import charlie.parser.Parser.*;
import charlie.parser.AriParser;
import charlie.terms.*;
import charlie.trs.*;

/**
 * This class reads text from string or file written in the .ari format used for the international
 * termination and confluence competitions.  For now, this is limited to the higher-order format.
 * In the future it may be expanded to first-order and constrained formats (which are also included
 * in ARI).
 */
public class AriInputReader extends TermTyper {
  /**
   * Stores the error collector for use by methods of the AriInputReader class.
   * Private because it should only be called by the static methods that use a AriInputReader.
   */
  private AriInputReader(ErrorCollector collector) {
    super(new SymbolData(), collector);
  }

  // ===================================== TRANSLATING A RULE =====================================

  /**
   * If the given identifier represents a free variable (that is, it does not occur in bound, and
   * is not declared as a function symbol), then this function stores numberArguments as its
   * arity.  If this is inconsistent with a previously declared arity for this variable, then an
   * error is stored instead.
   */
  private void registerVariableArity(Token token, String name, int numberArguments,
                                     TreeMap<String,Integer> arity, TreeSet<String> bound) {
    if (_symbols.lookupFunctionSymbol(name) != null) return;
    if (bound.contains(name)) return;
    if (arity.containsKey(name)) {
      if (arity.get(name) != 0) {
        storeError(token, "Inconsistent arity of variable " + name + ": occurs with no arguments " +
          "here, while it previously occurred with " + arity.get(name) + ".");
        return;
      }
    }
    arity.put(name, numberArguments);
  }

  /**
   * This goes through the given parser term, and for each unbound variable, it stores the number of
   * arguments with which it occurs.  By definition of the format, this arity should be consistent
   * in the full term.
   */
  private void storeVariableArity(ParserTerm term, TreeMap<String,Integer> arity,
                                  TreeSet<String> bound, int numArgs) {
    switch (term) {
      case Identifier(Token token, String name):
        registerVariableArity(token, name, numArgs, arity, bound);
        break;
      case Lambda(Token token, String varname, Type type, ParserTerm arg):
        if (bound.contains(varname)) storeVariableArity(arg, arity, bound, 0);
        else {
          bound.add(varname);
          storeVariableArity(arg, arity, bound, 0);
          bound.remove(varname);
        }
        break;
      case Application(Token token, ParserTerm head, FixedList<ParserTerm> args):
        storeVariableArity(head, arity, bound, args.size());
        for (ParserTerm t : args) storeVariableArity(t, arity, bound, 0);
        break;
      case PErr e:
        break;
      default:
        storeError(term.token(), "Unexpected term shape in ARI unconstrained higher-order format.");
    }
  }

  /**
   * This function returns an alteration of term where variable applications X(s1,...,sn) are
   * replaced by the meta-application X[s1,...,sn] if arity[X] = n.
   */
  private ParserTerm replaceMetaVariables(ParserTerm term, TreeMap<String,Integer> arity) {
    return switch (term) {
      case Identifier id -> id;
      case Lambda(Token token, String varname, Type type, ParserTerm arg) -> {
          Integer backup = arity.get(varname);
          if (backup != null) arity.remove(varname);
          ParserTerm ret = new Lambda(token, varname, type, replaceMetaVariables(arg, arity));
          if (backup != null) arity.put(varname, backup);
          yield ret;
        }
      case Application(Token token, ParserTerm head, FixedList<ParserTerm> args) -> {
          FixedList.Builder<ParserTerm> newargs = new FixedList.Builder<ParserTerm>();
          for (ParserTerm arg : args) newargs.add(replaceMetaVariables(arg, arity));
          if (head instanceof Identifier(Token t, String name) &&
              arity.containsKey(name) && arity.get(name) > 0) {
            yield new Meta(token, name, newargs.build());
          }
          else yield new Application(token, replaceMetaVariables(head, arity), newargs.build());
        }
      case PErr e -> term;
      default -> {
          storeError(term.token(), "Unexpected term shape.");
          yield new PErr(term);
        }
    };
  }

  private Rule makeRule(ParserRule rule) {
    TreeMap<String,Integer> variableArity = new TreeMap<String,Integer>();
    TreeSet<String> bound = new TreeSet<String>();
    storeVariableArity(rule.left(), variableArity, bound, 0);
    ParserTerm left = replaceMetaVariables(rule.left(), variableArity);
    ParserTerm right = replaceMetaVariables(rule.right(), variableArity); 
    _symbols.clearEnvironment();
    Term l = null, r = null;
    int a = _errors.queryErrorCount();
    if (!left.hasErrors()) l = makeTerm(left, null, true);
    if (!right.hasErrors()) {
      r = makeTerm(right, l == null ? null : l.queryType(), false);
    }
    int b = _errors.queryErrorCount();
    if (l == null || r == null) return null;
    try { return TrsFactory.createRule(l, r, TrsFactory.AMS); }
    catch (IllegalRuleException e) {
      if (a == b) storeError(rule.token(), e.getMessage());
      return null;
    }
  }

  // =================================== READING A FULL PROGRAM ===================================

  private void makeAlphabet(LookupMap<ParserDeclaration> fundecs) {
    for (ParserDeclaration decl : fundecs.values()) {
      String name = decl.name();
      Type type = decl.type();
      if (_symbols.lookupFunctionSymbol(name) != null) {
        storeError(decl.token(), "Duplicate function symbol: " + name);
      }
      else _symbols.addFunctionSymbol(TermFactory.createConstant(name, type));
    }
  }

  /** This function turns the entire ParserProgram into a TRS. */
  private TRS makeTRS(ParserProgram trs) {
    makeAlphabet(trs.fundecs());
    ArrayList<Rule> rules = new ArrayList<Rule>();
    for (ParserRule rho : trs.rules()) {
      Rule r = makeRule(rho);
      if (r != null) rules.add(r);
    }   
    Alphabet alphabet = _symbols.queryCurrentAlphabet();
    try { return TrsFactory.createTrs(alphabet, rules, TrsFactory.AMS); }
    catch (IllegalRuleException e) {
      storeError(null, e.getMessage());
      return null;
    }
  }

  // ==================================== PUBLIC FUNCTIONALITY ====================================

  /** Throws a ParsingException if there are any errors stored in the given error collector */
  private static void throwIfAnyErrors(ErrorCollector collector) {
    if (collector.queryErrorCount() > 0) throw collector.generateException();
  }

  /** Helper function for readTrsFromString and readTrsFromFile */
  private static TRS readParserProgram(ParserProgram trs, ErrorCollector collector) {
    throwIfAnyErrors(collector);
    AriInputReader rd = new AriInputReader(collector);
    TRS ret = rd.makeTRS(trs);
    throwIfAnyErrors(collector);
    return ret;
  }

  /**
   * Parses the given program, and returns the integer TRS that it defines.
   * If the string is not correctly formed, or the system cannot be unambiguously typed as an
   * LCTRS, this may throw a ParsingException.
   */
  public static TRS readTrsFromString(String str) {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = AriParser.readProgramFromString(str, collector);
    return readParserProgram(trs, collector);
  }

  /**
   * Parses the given file, which should be a .itrs file, into an LCTRS.
   * This may throw a ParsingException, or an IOException if something goes wrong with the file
   * reading.
   */
  public static TRS readTrsFromFile(String filename) throws IOException {
    ErrorCollector collector = new ErrorCollector();
    ParserProgram trs = AriParser.readProgramFromFile(filename, collector);
    return readParserProgram(trs, collector);
  }
}
