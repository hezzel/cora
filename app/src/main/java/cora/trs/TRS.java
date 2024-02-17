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
import java.util.TreeSet;
import java.util.Collection;
import cora.exceptions.IndexingError;
import cora.exceptions.NullInitialisationError;
import cora.utils.Pair;
import cora.terms.FunctionSymbol;
import cora.terms.Term;
import cora.terms.position.Position;

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
  private final TrsKind _kind;

  /**
   * Create a TRS with the given settings.  Default because this should only be called by the
   * factory.
   * (This is also why no null checks are done here.)
   */
  TRS(Alphabet alphabet, ImmutableList<Rule> rules, ImmutableList<RuleScheme> schemes,
      Collection<String> privateSymbols, TrsKind restrictions) {
    _alphabet = alphabet;
    _rules = rules;
    _schemes = schemes;
    _private = new TreeSet<String>(privateSymbols);
    _kind = restrictions;
  }

  /** @return the alphabet for this TRS. */
  public Alphabet queryAlphabet() {
    return _alphabet;
  }

  /** @return true if the function symbol is private in this TRS. */
  public boolean isPrivate(FunctionSymbol symbol) {
    return _private.contains(symbol.queryName());
  }

  /** @return the number of rules in the TRS that can be queried. */
  public int queryRuleCount() {
    return _rules.size();
  }

  /** For 0 ≤ index < queryRuleCount(), this returns one of the rules in the system. */
  public Rule queryRule(int index) {
    if (index < 0 || index >= queryRuleCount()) {
      throw new IndexingError("TRS", "queryRule", index, 0, queryRuleCount()-1);
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
      throw new IndexingError("TRS", "queryScheme", index, 0, querySchemeCount()-1);
    }
    return _schemes.get(index);
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
    return _kind.includeTheories();
  }

  /** Returns whether tuples and product types are supported in term construction. */
  public boolean tuplesIncluded() {
    return _kind.includeTuples();
  }

  /** Returns whether we are limited to first-order terms in term construction. */
  public boolean isFirstOrder() {
    return _kind.termsFirstOrder();
  }

  /** Returns whether we are limited to applicative terms in term construction. */
  public boolean isApplicative() {
    return _kind.termsApplicative();
  }

  /** Returns whether the given term is allowed to be used in this TRS. */
  public boolean termAllowed(Term term) {
    if (isFirstOrder()) {
      if (!term.isFirstOrder()) return false;
    }
    else if (isApplicative()) {
      if (!term.isApplicative()) return false;
    }
    if (tuplesIncluded() && theoriesIncluded()) return true;
    for (Pair<Term,Position> pair : term.querySubterms()) {
      Term sub = pair.fst();
      if (!theoriesIncluded() && sub.isFunctionalTerm() && sub.queryRoot().isTheorySymbol()) {
        return false;
      }
      if (!tuplesIncluded() && sub.queryType().hasProducts()) return false;
    }
    return true;
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
    if (_kind.includeTheories()) ret.append("} ∪ Σ_{theory}\n");
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

