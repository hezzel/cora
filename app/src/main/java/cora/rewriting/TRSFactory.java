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

package cora.rewriting;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import cora.exceptions.IllegalSymbolError;
import cora.exceptions.IllegalRuleError;
import cora.exceptions.NullInitialisationError;
import cora.terms.FunctionSymbol;

public class TRSFactory {
  /**
   * Does the checks needed for all kinds of TRSs, and throws an appropriate erorr if the checks
   * are not satisfied.
   */
  private static void doBasicChecks(Alphabet alphabet, List<Rule> rules, List<Scheme> schemes) {
    // none of the components is null
    if (alphabet == null) throw new NullInitialisationError("TRS", "alphabet");
    if (rules == null) throw new NullInitialisationError("TRS", "rules set");
    if (schemes == null) throw new NullInitialisationError("TRS", "rule schemes set");
    for (int i = 0; i < rules.size(); i++) {
      if (rules.get(i) == null) throw new NullInitialisationError("TRS", "rule " + i); 
    }
    for (int i = 0; i < schemes.size(); i++) {
      if (schemes.get(i) == null) throw new NullInitialisationError("TRS", "rule scheme " + i); 
    }

    // checks if our rules do not have variable or theory left-hand sides (this is permitted in
    // some of the rules to support rules that were created by some method, but not in the basic
    // TRSs)
    for (Rule rule : rules) {
      if (rule.queryLeftSide().isVariable()) {
        throw new IllegalRuleError("Rule " + rule.toString() + " has a variable as its " +
          "left-hand side.");
      }
      if (rule.queryLeftSide().isTheoryTerm()) {
        throw new IllegalRuleError("Rule " + rule.toString() + " has a theory term as " +
          "its left-hand side.");
      }
    }
  }

  /**
   * If c is true, updates schemes by adding the calculation rules.
   * If not, checks that all rules are indeed unconstrained, and throws an IllegalRuleError
   * otherwise.
   */
  private static void doConstraintChecks(boolean c, List<Rule> rules, List<Scheme> schemes) {
    if (c) schemes.add(new Calc());
    else {
      for (Rule rule : rules) {
        if (rule.isConstrained()) {
          throw new IllegalRuleError("Rule " + rule.toString() + " is constrained, " +
            "so cannot occur in an unconstrained TRS.");
        }
        if (rule.rightHasFreshVariables()) {
          throw new IllegalRuleError("Rule " + rule.toString() + " has fresh variables " +
            "in the right-hand side, which is not allowed in an unconstrained TRS.");
        }
      }
    }
  }

  /** Helper function for createMSTRS and createLCTRS */
  private static TRS createFirstorderTRS(Alphabet alphabet, List<Rule> rules, boolean constrained,
                                         Set<FunctionSymbol> priv) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();

    doBasicChecks(alphabet, rules, schemes);
    doConstraintChecks(constrained, rules, schemes);
    
    // assert that everything in the alphabet is first-order
    for (FunctionSymbol f : alphabet.getSymbols()) {
      if (f.queryType().queryTypeOrder() > 1) {
        throw new IllegalSymbolError("MSTRS/LCTRS", f.toString(), "Symbol with a type " +
          f.queryType().toString() + " cannot occur in a many-sorted TRS.");
      }   
    }   

    // assert that all the rules are first-order
    for (Rule rule : rules) {
      if (!rule.isFirstOrder()) {
        throw new IllegalRuleError("Rule " + rule.toString() + " cannot occur in " +
          "a many-sorted TRS, as it is not first-order.");
      }
    }

    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, constrained, priv);
  }

  /**
   * Creates a many-sorted or unsorted first-order term rewriting system with the given alphabet
   * and rules.  No rule schemes are included.  If the alphabet or rules are not first-order, then
   * an IllegalSymbolError or IllegalRulesError is thrown.
   */
  public static TRS createMSTRS(Alphabet alphabet, List<Rule> rules, Set<FunctionSymbol> priv) {
    return createFirstorderTRS(alphabet, rules, false, priv);
  }

  /**
   * Creates a Logically Constrained TRS: a first-order (many-sorted) TRS, with theory symbols and
   * constraints over the integers and booleans (and maybe some strings).
   *
   * Note that the given alphabet is the *non-theory* alphabet.  If this alphabet or the rules are
   * not first-order, then an IllegalSymbolError or IllegalRulesError is thrown.
   */
  public static TRS createLCTRS(Alphabet alphabet, List<Rule> rules, Set<FunctionSymbol> priv) {
    return createFirstorderTRS(alphabet, rules, true, priv);
  }

  /** Helper function for createApplicativeTRS and createLCSTRS */
  private static TRS createApplicativeTRS(Alphabet alphabet, List<Rule> rules, boolean constr,
                                          Set<FunctionSymbol> priv) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();

    doBasicChecks(alphabet, rules, schemes);
    doConstraintChecks(constr, rules, schemes);
    
    // assert that all the rules are applicative
    for (Rule rule : rules) {
      if (!rule.isApplicative()) {
        throw new IllegalRuleError("Rule " + rule.toString() + " cannot " +
          "occur in an applicative (simply-typed) TRS, as it is not applicative.");
      }
    }

    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, constr, priv);
  }

  /**
   * Creates an applicative higher-order term rewriting system with the given alphabet and rules.
   * No rule schemes are included, and rules are not constrained.  The rules are not required to be
   * patterns, only applicative.  If they are not, then an IllegalRuleError is thrown.
   */
  public static TRS createApplicativeTRS(Alphabet alphabet, List<Rule> rules,
                                         Set<FunctionSymbol> priv) {
    return createApplicativeTRS(alphabet, rules, false, priv);
  }
  
  /**
   * Creates an applicative higher-order term rewriting system with logical constraints, over the
   * given alphabet and rules.  Note that the alphabet is the *non-theory* alphabet; theory symbols
   * are automatically included.
   */
  public static TRS createLCSTRS(Alphabet alphabet, List<Rule> rules, Set<FunctionSymbol> priv) {
    return createApplicativeTRS(alphabet, rules, true, priv);
  }

  /**
   * Creates a Curried Functional System with the given alphabet, rules, the beta rule, and also
   * eta if this is indicated.
   */
  public static TRS createCFS(Alphabet alphabet, List<Rule> rules, boolean includeEta,
                              Set<FunctionSymbol> priv) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();
    schemes.add(new Beta());
    if (includeEta) schemes.add(new Eta());
    doBasicChecks(alphabet, rules, schemes);
    doConstraintChecks(false, rules, schemes);
    for (Rule rule : rules) {
      if (!rule.queryLeftSide().isTrueTerm()) {
        throw new IllegalRuleError("Rule " + rule.toString() +
          " cannot occur in a Curried Functional System, as it contains meta-variables.");
      }
    }
    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, false, priv);
  }

  /**
   * Creates an Applicative Meta-variable System with the given alphabet, rules, the beta rule,
   * and also eta if this is indicated.
   */
  public static TRS createAMS(Alphabet alphabet, List<Rule> rules, boolean includeEta,
                              Set<FunctionSymbol> priv) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();
    schemes.add(new Beta());
    if (includeEta) schemes.add(new Eta());
    doBasicChecks(alphabet, rules, schemes);
    doConstraintChecks(false, rules, schemes);
    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, false, priv);
  }

  /**
   * Creates an Applicative Meta-variable System with constraints and theory symbols over the
   * integers, booleans and strings.
   */
  public static TRS createCoraTRS(Alphabet alphabet, List<Rule> rules, boolean includeEta,
                                  Set<FunctionSymbol> priv) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();
    schemes.add(new Beta());
    if (includeEta) schemes.add(new Eta());
    doConstraintChecks(true, rules, schemes);
    doBasicChecks(alphabet, rules, schemes);
    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, true, priv);
  }
}

