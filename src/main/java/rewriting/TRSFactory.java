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
  }

  /** Helper function for createMSTRS and createLCTRS */
  private static TRS createFirstorderTRS(Alphabet alphabet, List<Rule> rules, boolean constrained) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();

    doBasicChecks(alphabet, rules, schemes);
    
    // assert that everything in the alphabet is first-order
    for (FunctionSymbol f : alphabet.getSymbols()) {
      if (f.queryType().queryTypeOrder() > 1) {
        throw new IllegalSymbolError("MSTRS", f.toString(), "Symbol with a type " +
          f.queryType().toString() + " cannot occur in a many-sorted TRS.");
      }   
    }   

    // assert that all the rules are first-order
    for (Rule rule : rules) {
      if (!rule.isFirstOrder()) {
        throw new IllegalRuleError("MSTRS", "Rule " + rule.toString() + " cannot occur in a " +
          "many-sorted TRS, as it is not first-order.");
      }
    }

    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, constrained);
  }

  /**
   * Creates a many-sorted or unsorted first-order term rewriting system with the given alphabet
   * and rules.  No rule schemes are included.  If the alphabet or rules are not first-order, then
   * an IllegalSymbolError or IllegalRulesError is thrown.
   */
  public static TRS createMSTRS(Alphabet alphabet, List<Rule> rules) {
    return createFirstorderTRS(alphabet, rules, false);
  }

  /**
   * Creates a Logically Constrained TRS: a first-order (many-sorted) TRS, with theory symbols and
   * constraints over the integers and booleans (and maybe some strings).
   *
   * Note that the given alphabet is the *non-theory* alphabet.  If this alphabet or the rules are
   * not first-order, then an IllegalSymbolError or IllegalRulesError is thrown.
   */
  public static TRS createLCTRS(Alphabet alphabet, List<Rule> rules) {
    return createFirstorderTRS(alphabet, rules, true);
  }

  /**
   * Creates an applicative higher-order term rewriting system with the given alpabet and rules.
   * No rule schemes are included.  The rules are not required to be patterns, only applicative.
   * If they are not, then an IllegalRuleError is thrown.
   */
  public static TRS createApplicativeTRS(Alphabet alphabet, List<Rule> rules) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();

    doBasicChecks(alphabet, rules, schemes);
    
    // assert that all the rules are applicative
    for (Rule rule : rules) {
      if (!rule.isApplicative()) {
        throw new IllegalRuleError("Applicative TRS", "Rule " + rule.toString() + " cannot " +
          "occur in an applicative (simply-typed) TRS, as it is not applicative.");
      }
    }

    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, false);
  }

  /**
   * Creates a Curried Functional System with the given alphabet, rules, the beta rule, and also
   * eta if this is indicated.
   */
  public static TRS createCFS(Alphabet alphabet, List<Rule> rules, boolean includeEta) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();
    schemes.add(new Beta());
    if (includeEta) schemes.add(new Eta());
    doBasicChecks(alphabet, rules, schemes);
    for (Rule rule : rules) {
      if (!rule.queryLeftSide().isTrueTerm()) {
        throw new IllegalRuleError("Curried Functionsal System", "Rule " + rule.toString() +
          " cannot occur in a Curried Functional System, as it contains meta-variables.");
      }
    }
    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, false);
  }

  /**
   * Creates an Applicative Meta-variable System with the given alphabet, rules, the beta rule,
   * and also eta if this is indicated.
   */
  public static TRS createAMS(Alphabet alphabet, List<Rule> rules, boolean includeEta) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();
    schemes.add(new Beta());
    if (includeEta) schemes.add(new Eta());
    doBasicChecks(alphabet, rules, schemes);
    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, false);
  }

  /**
   * Creates an Applicative Meta-variable System with constraints and theory symbols over the
   * integers, booleans and strings.
   */
  public static TRS createCoraTRS(Alphabet alphabet, List<Rule> rules, boolean includeEta) {
    ArrayList<Scheme> schemes = new ArrayList<Scheme>();
    schemes.add(new Beta());
    if (includeEta) schemes.add(new Eta());
    doBasicChecks(alphabet, rules, schemes);
    return new TRS(alphabet.copy(), new ArrayList<Rule>(rules), schemes, true);
  }
}

