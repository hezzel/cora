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
import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;
import charlie.exceptions.IndexingException;
import charlie.exceptions.IllegalRuleException;
import charlie.exceptions.IllegalSymbolException;
import charlie.exceptions.NullStorageException;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.FunctionSymbol;
import charlie.terms.Term;
import charlie.terms.position.Position;
import charlie.trs.TrsProperties.*;

/**
 * A TRS (term rewriting system), in essence, is a pair (T, →) of a set of terms and a reduction
 * relation on the terms.  The set of terms is built in a systematic way based on the kind of TRS,
 * and the relation is based on a (possibly infinite) set of rules.
 *
 * To represent a TRS in a finite class -- and be able to analyse them -- we impose some
 * restrictions.
 *
 * *** Building terms
 *
 * A TRS has an alphabet: a finite set of monomorphic function symbols, each with distinct names;
 * these symbols are called the "term symbols".  In addition, there may be a (possibly infinite)
 * set of theory symbols: calculation symbols and values, with an associated meaning in some SMT
 * theory: the "theory symbols".  There is no overlap between the names in terms symbols and
 * theory symbols.  For now, the set of theory symbols is either empty, of consists of the values
 * and calculations symbols for all the theories currently implemented in Cora.  This may change in
 * the future, however.
 * 
 * The set of terms to be reduced consists of TRUE TERMS (so no meta-variables), built in a
 * systematic way from variables and function symbols in the theory.  This systematic way is
 * defined as a restriction of general term formation by properties such as "first order" or "no
 * tuples allowed".
 *
 * *** Rules and reduction
 *
 * The reduction relation is given by: C[lγ] → C[rγ] if l → r | φ is a rule and γ is a substitution
 * that respects φ, and that maps all (meta-)variables in l and r to terms in T (so following the
 * restrictions of term formation in this style of TRS).
 *
 * The rules consist of a finite set of constrained rules (where the constraint may just be ⊤ for
 * an unconstrained rule), along with a finite number of rule schemes, where the latter essentially
 * represents a countably infinite number of rules.  All analysis methods should check whether the
 * rule schemes included in a TRS are supported, because it is possible that additional rule schemes
 * will be added in the future.
 *
 * *** Additional features
 *
 * We also keep track of public and private symbols.  All the theory symbols are automatically
 * public, but some of the terms symbols may be private.  While this does not affect T or →, the
 * "public terms" (true terms built from only public symbols) should be seen as the potential
 * starting points for analysis, which can be used in some analysis techniques.
 */
public class TRS {
  public enum RuleScheme { Beta, Eta, Calc, Projection };

  private final Alphabet _alphabet;
  private final ImmutableList<Rule> _rules;
  private final ImmutableList<RuleScheme> _schemes;
  private final TreeSet<String> _private;
  private TreeSet<FunctionSymbol> _defined;
  private String _trsKind;
  private TermLevel _level;
  private boolean _theoriesIncluded;
  private boolean _productsIncluded;
  private RuleRestrictions _rulesProperties;

  /**
   * Create a TRS with the given settings.  Default because this should only be called by the
   * factory.
   */
  TRS(Alphabet alphabet, List<Rule> rules, ImmutableList<RuleScheme> schemes,
      Collection<String> privateSymbols, String trsKindName, TermLevel trsLevel,
      boolean includeTheories, boolean includeProducts, RuleRestrictions restrictions) {

    if (alphabet == null) throw new NullStorageException("TRS", "alphabet");
    if (rules == null) throw new NullStorageException("TRS", "rules");

    _theoriesIncluded = includeTheories;
    _productsIncluded = includeProducts;
    _level = trsLevel;
    _alphabet = alphabet;
    _schemes = schemes;
    _trsKind = trsKindName;
    if (privateSymbols == null) _private = new TreeSet<String>();
    else _private = new TreeSet<String>(privateSymbols);
    _defined = new TreeSet<FunctionSymbol>();

    // ensure that the alphabet follows the requirements we just stored
    verifyAlphabet();

    // build the rules list, and collect the actual rule restrictions while we're at it
    _rulesProperties = new RuleRestrictions();
    ImmutableList.Builder<Rule> rulebuilder = ImmutableList.<Rule>builder();
    for (Rule rule : rules) {
      if (rule == null) throw new NullStorageException("TRS", "one of the rules");
      _rulesProperties = _rulesProperties.supremum(rule.queryProperties());
      rulebuilder.add(rule);
      FunctionSymbol root = rule.queryRoot();
      if (root != null) _defined.add(root);
    }
    _rules = rulebuilder.build();

    // and give an error if we don't satisfy the given restrictions on the rules
    if (restrictions != null) {
      String problem = restrictions.checkCoverage(_rulesProperties);
      if (problem != null) throw new IllegalRuleException(problem);
    }
  }

  /** This checks that the alphabet follows the properties stored for the TRS terms. */
  private void verifyAlphabet() {
    for (FunctionSymbol f : _alphabet.getSymbols()) {
      Type type = f.queryType();
      if (_level == TermLevel.FIRSTORDER && type.queryTypeOrder() > 1) {
        throw new IllegalSymbolException("TRS", f.toString(), "Symbol " + f.toString() +
          " with a type " + type.toString() + " cannot occur in a first-order TRS.");
      }
      if (!_productsIncluded && type.hasProducts()) {
        throw new IllegalSymbolException("TRS", f.toString(), "Symbol with a type " +
          type.toString() + " cannot occur in a product-free TRS.");
      }
    }
  }

  /** @return the alphabet for this TRS. */
  public Alphabet queryAlphabet() {
    return _alphabet;
  }

  /** @return our underlying set of all private symbols -- this Set is immutable! */
  public Set<String> queryPrivateSymbols() {
    return Collections.unmodifiableSet(_private);
  }

  /** @return true if the function symbol is private in this TRS. */
  public boolean isPrivate(FunctionSymbol symbol) {
    return _private.contains(symbol.queryName());
  }

  /** @return true if the function symbol is the root symbol of the lhs of some rule. */
  public boolean isDefined(FunctionSymbol symbol) {
    return _defined.contains(symbol);
  }

  /** @return the number of rules in the TRS that can be queried. */
  public int queryRuleCount() {
    return _rules.size();
  }

  /** For 0 ≤ index < queryRuleCount(), this returns one of the rules in the system. */
  public Rule queryRule(int index) {
    if (index < 0 || index >= queryRuleCount()) {
      throw new IndexingException("TRS", "queryRule", index, 0, queryRuleCount()-1);
    }
    return _rules.get(index);
  }

  /** @return the number of schemes in the TRS that can be queried. */
  public int querySchemeCount() {
    return _schemes.size();
  }

  /** For 0 ≤ index < querySchemeCount(), this returns one of the schemes in the system. */
  public RuleScheme queryScheme(int index) {
    if (index < 0 || index >= querySchemeCount()) {
      throw new IndexingException("TRS", "queryScheme", index, 0, querySchemeCount()-1);
    }
    return _schemes.get(index);
  }

  /** Returns the kind of TRS this is (e.g., MSTRS, CFS */
  public String queryTrsKind() {
    return _trsKind;
  }

  /** Returns a copy of the set of defined symbols. */
  public TreeSet<FunctionSymbol> definedSymbols() {
    return new TreeSet<FunctionSymbol>(_defined);
  }

  /** Returns the names of all non-theory symbols declared in the alphabet. */
  public Set<String> queryFunctionSymbolNames() {
    return _alphabet.getSymbols().stream().map(FunctionSymbol::queryName)
                    .collect(Collectors.toSet());
  }

  /**
   * Returns the FunctionSymbol associated to the given name in this TRS, if there is a unique
   * one.  This does not include theory symbols since these are allowed to be polymorphic!
   */
  public FunctionSymbol lookupSymbol(String name) {
    return _alphabet.lookup(name);
  }

  /** Returns whether theory symbols are supported in term construction. */
  public boolean theoriesIncluded() {
    return _theoriesIncluded;
  }

  /** Returns whether tuples and product types are supported in term construction. */
  public boolean productsIncluded() {
    return _productsIncluded;
  }

  /** Returns whether we are limited to first-order terms in term construction. */
  public boolean isFirstOrder() {
    return _level == TermLevel.FIRSTORDER;
  }

  /** Returns whether we are limited to applicative terms in term construction. */
  public boolean isApplicative() {
    return _level.compareTo(TermLevel.APPLICATIVE) <= 0;
  }

  /** Returns whether all rules are left-linear. */
  public boolean isLeftLinear() {
    for (int i = 0; i < _rules.size(); i++) {
      if (!_rules.get(i).isLeftLinear()) return false;
    }
    return true;
  }

  /** 
   * Creates a TRS with alphabet, restrictions and rule schemes the same as we have, but with the
   * given rules replacing the original ones.  No restrictions are imposed on the new rules.
   */
  public TRS createDerivative(List<Rule> newrules) {
    return new TRS(_alphabet, newrules, _schemes, _private, _trsKind, _level, _theoriesIncluded,
                   _productsIncluded, null);
  }

  /**
   * Returns true if all of the following hold:
   * (a) all the rules satisfy AT MOST the given properties (e.g., if Level.APPLICATIVE is given
   *     is is okay to have first-order rules, but not rules with lambdas)
   * (b) term construction in the current TRS also follows the given properties (e.g., if
   *     Constrained.NO is given, then the TRS should not include theory symbols even if the
   *     rules don't use them); if Level.META is given then any level of terms is included
   * (c) the TRS does not have the Eta rule scheme, or Eta is given as an additional argument
   * Returns false otherwise.
   *
   * Note: some settings automatically imply the inclusion of certain rule schemes:
   *   - if lvl = Level.LAMBDA or lvl = Level.META, then Beta is automatically included
   *   - if theories = Constrained.YES, then Calc is automatically included
   *   - if products = Products.ALLOWED, then Projection is automatically included
   * Hence, any method indicating these settings should also support the presence of these rule
   * schemes.  However, these do not need to be listed in the call to verifyProperties.
   */
  public boolean verifyProperties(Level lvl, Constrained theories, Products products, Lhs pattern,
                                  Root rootstat, RuleScheme ...additionalSchemes) {
    if (_theoriesIncluded && theories == Constrained.NO) return false;
    if (_productsIncluded && products == Products.DISALLOWED) return false;
    if (TrsProperties.translateRuleToTermLevel(lvl).compareTo(_level) < 0) return false;
    if (!schemesIncluded(additionalSchemes)) return false;
    RuleRestrictions rest = new RuleRestrictions(lvl, theories, products, pattern, rootstat);
    return rest.covers(_rulesProperties);
  }

  /**
   * Returns true if all of the following hold:
   * (a) all the rules satisfy AT MOST the given properties (e.g., if Level.APPLICATIVE is given
   *     is is okay to have first-order rules, but not rules with lambdas)
   * (b) term construction in the current TRS follows the given "term" properties
   * (c) the TRS does not have the Eta rule scheme, or Eta is given as an additional argument
   * Returns false otherwise.
   *
   * Note: some settings automatically imply the inclusion of certain rule schemes:
   *   - if termLevel = TermLevel.LAMBDA, then Beta is automatically included
   *   - if termTheories = Constrained.YES, then Calc is automatically included
   *   - if termProducts = Products.ALLOWED, then Projection is automatically included
   * Hence, any method indicating these settings should also support the presence of these rule
   * schemes.  However, these do not need to be listed in the call to verifyProperties.
   */
  public boolean verifyProperties(Level ruleLevel, Constrained ruleTheories, Products ruleProducts,
                                  Lhs pattern, Root rootstat, TermLevel termLevel,
                                  Constrained termTheories, Products termProducts,
                                  RuleScheme ...additionalSchemes) {
    if (_theoriesIncluded && termTheories == Constrained.NO) return false;
    if (_productsIncluded && termProducts == Products.DISALLOWED) return false;
    if (termLevel.compareTo(_level) < 0) return false;
    if (!schemesIncluded(additionalSchemes)) return false;
    RuleRestrictions rest =
      new RuleRestrictions(ruleLevel, ruleTheories, ruleProducts, pattern, rootstat);
    return rest.covers(_rulesProperties);
  }

  /** Returns true if all our rule schemes are included in supported */
  private boolean schemesIncluded(RuleScheme[] supported) {
    if (!_schemes.contains(RuleScheme.Eta)) return true;
    for (RuleScheme s : supported) {
      if (s == RuleScheme.Eta) return true;
    }
    return false;
  }

  /** Returns whether the given term is allowed to be used in this TRS. */
  public boolean termAllowed(Term term) {
    if (isFirstOrder()) {
      if (!term.isFirstOrder()) return false;
    }
    else if (isApplicative()) {
      if (!term.isApplicative()) return false;
    }
    if (_productsIncluded && _theoriesIncluded) return true;
    return null == term.findSubterm((sub,pos) ->
      ( (!_theoriesIncluded && sub.isFunctionalTerm() && sub.queryRoot().isTheorySymbol()) ||
        (!_productsIncluded && sub.queryType().hasProducts())
      )
    );
  }

  /** Gives a human-readable representation of the term rewriting system. */
  public String toString() {
    StringBuilder ret = new StringBuilder();
    ret.append("Σ = {\n");
    for (FunctionSymbol f : _alphabet.getSymbols()) {
      ret.append("  " + f.queryName() + " :: " + f.queryType());
      if (_private.contains(f.queryName())) ret.append("  (private)");
      ret.append("\n");
    }
    if (_theoriesIncluded) ret.append("} ∪ Σ_{theory}\n");
    else ret.append("}\n");
    ret.append("R = {\n");
    for (int i = 0; i < _rules.size(); i++) {
      ret.append("  ");
      ret.append(_rules.get(i).toString());
      ret.append("\n");
    }
    ret.append("}\n");
    if (_schemes.size() != 0) ret.append("We also include the following rule schemes: ");
    for (int i = 0; i < _schemes.size(); i++) {
      if (i != 0) ret.append(", ");
      ret.append(_schemes.get(i).toString());
    }
    ret.append("\n");
    return ret.toString();
  }
}

