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

package charlie.trs;

import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import charlie.exceptions.IllegalRuleException;
import charlie.terms.Term;
import charlie.trs.TrsProperties.*;

/** The TrsFactory is used to create both rules and various kinds of TRSs. */
public class TrsFactory {
  /**
   * A TrsKind contains the name and default properties of certain kinds of TRSs (e.g., an MSTRS is
   * first-order and unconstrained).  This is used in the constructors for TRSs and perhaps rules to
   * ensure that the right correctness checks are done.
   */
  public static class TrsKind {
    private String _name;
    private RuleRestrictions _restrictions;
    private TrsKind(String name, Level lvl, Constrained theories, TypeLevel tlvl, Lhs pattern,
                    Root rootstat) {
      _name = name;
      _restrictions = new RuleRestrictions(lvl, theories, tlvl, pattern, rootstat);
    }
    public boolean theoriesIncluded() { return _restrictions.theoriesUsed(); }
    public String toString() { return _name + " with " + _restrictions.toString(); }
  }

  public static final TrsKind MSTRS = new TrsKind("MSTRS",
    Level.FIRSTORDER,  Constrained.NO,  TypeLevel.SIMPLE,         Lhs.PATTERN,     Root.FUNCTION);
  public static final TrsKind STRS = new TrsKind("STRS",
    Level.APPLICATIVE, Constrained.NO,  TypeLevel.SIMPLE,         Lhs.SEMIPATTERN, Root.ANY);
  public static final TrsKind CFS = new TrsKind("CFS",
    Level.LAMBDA,      Constrained.NO,  TypeLevel.SIMPLE,         Lhs.SEMIPATTERN, Root.ANY);
  public static final TrsKind AMS = new TrsKind("AMS",
    Level.META,        Constrained.NO,  TypeLevel.SIMPLE,         Lhs.SEMIPATTERN, Root.ANY);
  public static final TrsKind LCTRS = new TrsKind("LCTRS",
    Level.FIRSTORDER,  Constrained.YES, TypeLevel.SIMPLE,         Lhs.PATTERN,     Root.THEORY);
  public static final TrsKind LCSTRS = new TrsKind("LCSTRS",
    Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE,         Lhs.SEMIPATTERN, Root.ANY);
  public static final TrsKind CORA = new TrsKind("Cora-TRS",
    Level.META,        Constrained.YES, TypeLevel.SIMPLEPRODUCTS, Lhs.NONPATTERN,  Root.ANY);

  /**
   * Check if the given rule is allowed in the given kind of TRS.  If not, throws an
   * IllegalRuleException.
   */
  private static void checkRestrictions(Rule rule, TrsKind kind) {
    String problem = kind._restrictions.checkCoverage(rule.queryProperties());
    if (problem == null) return;
    throw new IllegalRuleException("The rule " + rule.toString() + " is not allowed to occur in " +
      kind._name + "s: " + problem + ".");
  }

  /**
   * This function creates an unconstrained rule left → right.
   * The rule is checked against the given TRS kind: if the rule is not allowed in the give nkind
   * of TRS, then an IllegalRuleException is thrown.
   */
  public static Rule createRule(Term left, Term right, TrsKind restrictions) {
    Rule rule = new Rule(left, right);
    checkRestrictions(rule, restrictions);
    return rule;
  }

  /** This function creates an unconstrained rule left → right. */
  public static Rule createRule(Term left, Term right) {
    return new Rule(left, right);
  }

  /**
   * This function creates a constrained rule left → right | constraint.
   * The rule is checked against the given TRS kind: if the rule is not allowed in the given kind
   * of TRS, then an IllegalRuleException is thrown.
   */
  public static Rule createRule(Term left, Term right, Term constraint, TrsKind restrictions) {
    Rule rule = new Rule(left, right, constraint);
    checkRestrictions(rule, restrictions);
    return rule;
  }

  /** This function creates a constrained rule left → right | constraint. */
  public static Rule createRule(Term left, Term right, Term constraint) {
    return new Rule(left, right, constraint);
  }

  /**
   * Creates a TRS with the given restrictions, rules and private symbols, and adds the Eta rule
   * scheme if this is required. (Other rule schemes are included based on the kind of TRS.)
   */
  public static TRS createTrs(Alphabet alphabet, List<Rule> rules, Set<String> privateSymbols,
                              boolean includeEta, TrsKind kind) {
    // build the list of rule schemes
    ImmutableList.Builder<TRS.RuleScheme> newschemes = ImmutableList.<TRS.RuleScheme>builder();
    if (kind._restrictions.queryLevel().compareTo(Level.LAMBDA) >= 0) {
      newschemes.add(TRS.RuleScheme.Beta);
      if (includeEta) newschemes.add(TRS.RuleScheme.Eta);
    }
    else if (includeEta) {
      throw new IllegalRuleException("Eta can only be added to TRSs whose term formation " +
        "includes abstraction.");
    }
    if (kind._restrictions.theoriesUsed()) newschemes.add(TRS.RuleScheme.Calc);

    return new TRS(alphabet, rules, newschemes.build(), privateSymbols, kind._name,
                   TrsProperties.translateRuleToTermLevel(kind._restrictions.queryLevel()),
                   kind._restrictions.theoriesUsed(), kind._restrictions.productsUsed(),
                   kind._restrictions);
  }

  /** Creates a TRS with the given restrictions, with no private symbols or extra rule schemes. */
  public static TRS createTrs(Alphabet alphabet, List<Rule> rules, TrsKind kind) {
    return createTrs(alphabet, rules, new TreeSet<String>(), false, kind);
  }
}

