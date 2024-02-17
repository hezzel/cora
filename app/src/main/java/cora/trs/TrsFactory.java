/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.trs;

import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import cora.exceptions.IllegalRuleError;
import cora.exceptions.IllegalSymbolError;
import cora.exceptions.NullInitialisationError;
import cora.types.Type;
import cora.terms.Term;
import cora.terms.FunctionSymbol;

/** The TrsFactory is used to create both rules and various kinds of TRSs. */
public class TrsFactory {
  public static final TrsKind MSTRS =
    new TrsKind("MSTRS", TrsKind.LVL_FIRSTORDER, TrsKind.THEORIES_NONE,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_FUNCTION);
  public static final TrsKind STRS =
    new TrsKind("STRS", TrsKind.LVL_APPLICATIVE, TrsKind.THEORIES_NONE,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_ANY, TrsKind.LHS_SEMIPATTERN);
  public static final TrsKind CFS =
    new TrsKind("CFS", TrsKind.LVL_LAMBDA, TrsKind.THEORIES_NONE,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_ANY, TrsKind.LHS_PATTERN);
  public static final TrsKind AMS =
    new TrsKind("AMS", TrsKind.LVL_META, TrsKind.THEORIES_NONE,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_ANY, TrsKind.LHS_SEMIPATTERN);
  public static final TrsKind LCTRS =
    new TrsKind("LCTRS", TrsKind.LVL_FIRSTORDER, TrsKind.THEORIES_YES,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_THEORY);
  public static final TrsKind LCSTRS =
    new TrsKind("LCSTRS", TrsKind.LVL_APPLICATIVE, TrsKind.THEORIES_YES,
                TrsKind.PRODUCTS_DISALLOWED, TrsKind.ROOT_ANY, TrsKind.LHS_SEMIPATTERN);
  public static final TrsKind CORA =
    new TrsKind("Cora-TRS", TrsKind.LVL_META, TrsKind.THEORIES_YES,
                TrsKind.PRODUCTS_ALLOWED, TrsKind.ROOT_ANY, TrsKind.LHS_NONPATTERN);

  /**
   * Check if the given rule is allowed in the given kind of TRS.  If not, throws an
   * IllegalRuleError.
   */
  private static void checkRestrictions(Rule rule, TrsKind kind) {
    String problem = kind.queryRestrictions().checkCoverage(rule.queryProperties());
    if (problem == null) return;
    throw new IllegalRuleError("The rule " + rule.toString() + " is not allowed to occur in " +
      kind.queryName() + "s: " + problem + ".");
  }

  /**
   * This function creates an unconstrained rule left → right.
   * The rule is checked against the given TRS kind: if the rule is not allowed in the give nkind
   * of TRS, then an IllegalRuleError is thrown.
   */
  public static Rule createRule(Term left, Term right, TrsKind restrictions) {
    Rule rule = new Rule(left, right);
    checkRestrictions(rule, restrictions);
    return rule;
  }

  /** This function creates an unconstrained rule left → right. */
  public static Rule createRule(Term left, Term right) {
    Rule rule = new Rule(left, right);
    return rule;
  }

  /**
   * This function creates a constrained rule left → right | constraint.
   * The rule is checked against the given TRS kind: if the rule is not allowed in the given kind
   * of TRS, then an IllegalRuleError is thrown.
   */
  public static Rule createRule(Term left, Term right, Term constraint, TrsKind restrictions) {
    Rule rule = new Rule(left, right, constraint);
    checkRestrictions(rule, restrictions);
    return rule;
  }

  /** This function creates a constrained rule left → right | constraint. */
  public static Rule createRule(Term left, Term right, Term constraint) {
    Rule rule = new Rule(left, right, constraint);
    return rule;
  }

  /**
   * Creates a TRS with the given restrictions, rules and private symbols, and adds the Eta rule
   * scheme if this is required. (Other rule schemes are included based on the kind of TRS.)
   */
  public static TRS createTrs(Alphabet alphabet, List<Rule> rules, Set<String> privateSymbols,
                              boolean includeEta, TrsKind kind) {
    if (alphabet == null) throw new NullInitialisationError("TRS", "alphabet");
    if (rules == null) throw new NullInitialisationError("TRS", "rules");
    if (privateSymbols == null) privateSymbols = new TreeSet<String>();
    if (kind == null) throw new NullInitialisationError("TRS", "trs kind");

    // build the rules list, and ensure that all rules follow the given TRS kind
    ImmutableList.Builder<Rule> newrules = ImmutableList.<Rule>builder();
    for (Rule rule : rules) {
      if (rule == null) throw new NullInitialisationError("TRS", "one of the rules");
      String problem = kind.queryRestrictions().checkCoverage(rule.queryProperties());
      if (problem != null) throw new IllegalRuleError(problem);
      newrules.add(rule);
    }
    // build the list of rule schemes
    ImmutableList.Builder<TRS.RuleScheme> newschemes = ImmutableList.<TRS.RuleScheme>builder();
    if (kind.termsIncludeLambda()) {
      newschemes.add(TRS.RuleScheme.Beta);
      if (includeEta) newschemes.add(TRS.RuleScheme.Beta);
    }
    else if (includeEta) {
      throw new IllegalRuleError("Eta can only be added to TRSs whose term formation includes " +
        "abstraction.");
    }
    if (kind.includeTheories()) newschemes.add(TRS.RuleScheme.Calc);
    if (kind.includeTuples()) newschemes.add(TRS.RuleScheme.Projection);
    // ensure that the alphabet follows the given TRS kind
    for (FunctionSymbol f : alphabet.getSymbols()) {
      Type type = f.queryType();
      if (kind.termsFirstOrder() && type.queryTypeOrder() > 1) {
        throw new IllegalSymbolError("TRS", f.toString(), "Symbol with a type " + type.toString() +
          " cannot occur in a first-order TRS.");
      }
      if (!kind.includeTuples() && type.hasProducts()) {
        throw new IllegalSymbolError("TRS", f.toString(), "Symbol with a type " + type.toString() +
          " cannot occur in a product-free TRS.");
      }
    }

    return new TRS(alphabet, newrules.build(), newschemes.build(), privateSymbols, kind);
  }

  /** Creates a TRS with the given restrictions, with no private symbols or extra rule schemes. */
  public static TRS createTrs(Alphabet alphabet, List<Rule> rules, TrsKind kind) {
    return createTrs(alphabet, rules, new TreeSet<String>(), false, kind);
  }
}

