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

package cora.termination.transformation;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeMap;
import java.util.TreeSet;
import charlie.util.Pair;
import charlie.types.Type;
import charlie.terms.position.*;
import charlie.terms.*;
import charlie.trs.*;
import cora.io.OutputModule;
import cora.io.ProofObject;

/**
 * This class is used to transform a TRS so as not to have rules f(s1,...,sn) → C[f(s1,...,sk)]
 * with k < n, since such rules cannot be handled with static dependency pairs.
 * If possible, this class will seek to replace such symbols f on the right by helper symbols.
 * This is still only a prototype implementation; the general version of the technique has not
 * been defined yet.
 *
 * Note: this transformation is not sound for universal computability! Even if only private symbols
 * are changed, it may impact left-linearity.
 *
 * Also note: since thiis transformation involves quite a few steps, the methods implementing
 * individual steps are default rather than private for the sake of unit testing.  They are not
 * intended to be called.by other functions in the package unless explicitly stated otherwise.
 */
public class HelperFunctionTransformer {
  private boolean _applicable;
  private TreeMap<FunctionSymbol,Integer> _ruleArity;
  private TRS _trs;

  public HelperFunctionTransformer(TRS trs) {
    _trs = trs;
    _applicable = trs.isLeftLinear() && trs.verifyProperties(TrsProperties.Level.APPLICATIVE,
      TrsProperties.Constrained.YES, TrsProperties.Products.DISALLOWED, TrsProperties.Lhs.PATTERN,
      TrsProperties.Root.THEORY);
    getSymbolArities();
  }

  /**
   * Stores the smallest number of arguments each defined symbol f occurs with at the left-hand
   * of a rule (at the root) in _minar.
   *
   * If any rule does not have a function symbol as root symbol, then null is returned instead.
   */
  private void getSymbolArities() {
    _ruleArity = new TreeMap<FunctionSymbol,Integer>();
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      Rule rule = _trs.queryRule(i);
      Term l = rule.queryLeftSide();
      if (!l.isFunctionalTerm()) { _applicable = false; return; }
      FunctionSymbol f = l.queryRoot();
      int num = l.numberArguments();
      if (!_ruleArity.containsKey(f)) _ruleArity.put(f, num);
      else {
        int k = _ruleArity.get(f);
        if (k > num) _ruleArity.put(f, num);
      }
    }
  }

  /** Helper function only for the sake of unit testing */
  Integer queryRuleArity(FunctionSymbol f) { return _ruleArity.get(f); }

  /** Helper class to conveniently return a result for getReplacement */
  record Candidate(FunctionSymbol below, int argument, FunctionSymbol main, int numArgs) {
    public boolean equals(Candidate other) {
      return below.equals(other.below) && argument == other.argument &&
             main.equals(other.main) && numArgs == other.numArgs;
    }
  }

  /**
   * Helper function for getReplacementCandidates(): this adds the given tuple (g,i,f,n) to the
   * given candidate list if it is not already in there.
   */
  private void add(ArrayList<Candidate> lst, FunctionSymbol g, int i, FunctionSymbol f, int n) {
    Candidate c = new Candidate(g, i, f, n);
    for (Candidate a : lst) { if (a.equals(c)) return; }
    lst.add(c);
  }

  /**
   * Helper function for getReplacementCandidates(): returns true if there exist w1 ... wn such that
   * u = v w1 ... wn, with n > 0.  We assume that u has the form f(s1,...,sk).
   */
  private boolean isHeadOf(Term v, Term u) {
    if (!v.isFunctionalTerm() || !v.queryRoot().equals(u.queryRoot())) return false;
    if (u.numberArguments() <= v.numberArguments()) return false;
    return u.queryImmediateHeadSubterm(v.numberArguments()).equals(v);
  }
  
  /**
   * This returns all the pairs (f,i,g,n) such that a rule f(s1,...,sk) → C[g(...,f(s1,...,sn),...)]
   * exists, with n < k and f occurring at argument position i and n < ruleArity(f).
   */
  ArrayList<Candidate> getReplacementCandidates() {
    ArrayList<Candidate> ret = new ArrayList<Candidate>();
    for (int j = 0; j < _trs.queryRuleCount(); j++) {
      Rule rule = _trs.queryRule(j);
      Term left = rule.queryLeftSide();
      FunctionSymbol f = left.queryRoot();
      int k = left.numberArguments();
      rule.queryRightSide().visitSubterms((s,p) -> {
        if (!s.isFunctionalTerm()) return;
        FunctionSymbol g = s.queryRoot();
        for (int i = 1; i <= s.numberArguments(); i++) {
          Term arg = s.queryArgument(i);
          int n = arg.numberArguments();
          if (isHeadOf(arg, left) && n < _ruleArity.get(f)) add(ret, g, i, f, n);
        }
      });
    }

    return ret;
  }

  /**
   * This checks whether a given function candidate (f,i,g,n) is suitable for replacement:
   * - g always occurs with at least i arguments in the left-hand side
   * - argument i of g is always a variable, or not unifiable with f(X1,...,Xn)
   * NOTE: if it is ever allowed for higher-order variables to occur in the constraint, then this
   * should probably be adapted to disallow variables that occur inside the constraint.
   */
  boolean checkCandidateSuitability(Candidate cand) {
    FunctionSymbol g = cand.below();
    FunctionSymbol f = cand.main();
    int i = cand.argument();

    for (int j = 0; j < _trs.queryRuleCount(); j++) {
      Term left = _trs.queryRule(j).queryLeftSide();
      Term constraint = _trs.queryRule(j).queryConstraint();
      if (null != left.findSubterm((s,p) -> { // return true if the subterm is unsuitable
        if (!s.isFunctionalTerm() || !s.queryRoot().equals(g)) return false;
        if (s.numberArguments() < i) return true;
        Term arg = s.queryArgument(i);
        if (arg.isVariable() || arg.isAbstraction()) return false;
        // we could probably handle this case as well, but for now, the theory does not allow it
        if (arg.isFunctionalTerm()) return arg.queryRoot().equals(f);
        return true;
      })) return false;
    }

    return true;
  }

  /** This creaes a replacement function symbol f' for reach "main" symbol f in cands. */
  TreeMap<FunctionSymbol,FunctionSymbol> createCopies(List<Candidate> cands) {
    TreeSet<FunctionSymbol> symbols = new TreeSet<FunctionSymbol>();
    TreeSet<String> newnames = new TreeSet<String>();
    TreeMap<FunctionSymbol,FunctionSymbol> ret = new TreeMap<FunctionSymbol,FunctionSymbol>();
    for (Candidate cand : cands) symbols.add(cand.main());
    for (FunctionSymbol f : symbols) {
      String newname = f.queryName() + "'";
      for (int i = 0; _trs.lookupSymbol(newname) != null || newnames.contains(newname); i++) {
        newname = f.queryName() + "'" + i;
      }
      newnames.add(newname);
      FunctionSymbol helper = TermFactory.createConstant(newname, f.queryType());
      ret.put(f, helper);
    }
    return ret;
  }

  /** Returns the private symbols of the TRS, along with all the copied symbols */
  private TreeSet<String> determinePrivate(TreeMap<FunctionSymbol,FunctionSymbol> copies) {
    TreeSet<String> ret = new TreeSet<String>(_trs.queryPrivateSymbols());
    for (FunctionSymbol f : copies.values()) ret.add(f.queryName());
    return ret;
  }

  /**
   * This returns a list with single-replacement substitutions: one for each variable that occurs
   * at a candidate position in the given term, provided it also occurs in the given varlist.
   */
  private ArrayList<Substitution> getReplacementSubstitutions(Term term, ReplaceableList okay,
                                                              List<Candidate> cands) {
    ArrayList<Substitution> ret = new ArrayList<Substitution>();
    for (Pair<Term,Position> sub : term.querySubterms()) {
      Term subterm = sub.fst();
      if (!subterm.isFunctionalTerm()) continue;
      for (int j = 0; j < cands.size(); j++) {
        Candidate cand = cands.get(j);
        if (!subterm.queryRoot().equals(cand.below())) continue;
        // the argument must be a veriable if term is a rule lhs and the candidate was suitable
        Variable arg = subterm.queryArgument(cand.argument()).queryVariable();
        if (!okay.contains(arg)) continue;
        Term replacement = cand.main();
        for (int i = 0; i < cand.numArgs(); i++) {
          String varname = "arg." + (j+1) + "." + (i+1);
          Variable x = TermFactory.createVar(varname, replacement.queryType().subtype(1));
          replacement = replacement.apply(x);
        }
        Substitution subst = TermFactory.createEmptySubstitution();
        subst.extend(arg, replacement);
        ret.add(subst);
      }
    }
    return ret;
  }

  /** Creates copies of all rules in rules with any combination of substitutions applied */
  private void applyAllUpdates(ArrayList<Rule> rules, ArrayList<Substitution> substitutions) {
    for (Substitution subst : substitutions) {
      int n = rules.size();
      for (int i = 0; i < n; i++) {
        Rule rule = rules.get(i);
        Term lhs = rule.queryLeftSide();
        Term rhs = rule.queryRightSide();
        Term lhssubst = lhs.substitute(subst);
        if (!lhssubst.equals(lhs)) {
          Term rhssubst = rhs.substitute(subst);
          rules.add(TrsFactory.createRule(lhssubst, rhssubst, rule.queryConstraint()));
        }
      }
    }
  }

  /**
   * For each occurrence candidate (g, i, f, n), and each occurrence of a subterm
   * g(s1,...,f(t1,...,tn),...sm) in term, this replaces f by renamings[f].
   * The result of all renamings is returned;
   */
  Term renameSymbolsInsideCandidates(Term term, List<Candidate> candidates,
                                     TreeMap<FunctionSymbol,FunctionSymbol> renamings) {
    for (Pair<Term,Position> p : term.querySubterms()) {
      Term subterm = p.fst();
      if (!subterm.isFunctionalTerm()) continue;
      FunctionSymbol g = subterm.queryRoot();
      for (Candidate cand : candidates) {
        if (!g.equals(cand.below())) continue;
        int index = cand.argument();
        if (subterm.numberArguments() < index) continue;
        Term arg = subterm.queryArgument(index);
        if (!arg.isFunctionalTerm() || !arg.queryRoot().equals(cand.main())) continue;
        Position pos = p.snd().append(new ArgumentPos(index, new FinalPos(cand.numArgs())));
        term = term.replaceSubterm(pos, renamings.get(cand.main()));
      }
    }
    return term;
  }

  /** This calls renameSymbolsInsideCandidates on all left- and right-hand sides of rules. */
  private void renameAll(ArrayList<Rule> rules, List<Candidate> candidates,
                         TreeMap<FunctionSymbol,FunctionSymbol> renamings) {
    for (int i = 0; i < rules.size(); i++) {
      Rule rule = rules.get(i);
      Term lhs = renameSymbolsInsideCandidates(rule.queryLeftSide(), candidates, renamings);
      Term rhs = renameSymbolsInsideCandidates(rule.queryRightSide(), candidates, renamings);
      Term constraint = rule.queryConstraint();
      rules.set(i, TrsFactory.createRule(lhs, rhs, constraint));
    }
  }

  /**
   * For any combination of positions in the lhs of the given rule and appropriate replacement
   * candidates, this creates a copy of the given rule that matches specifically on the candidate.
   * The result is a list (exponential in min(length of cand, size of the lhs)) that contains all
   * these intantiated rule combinations.
   */
  ArrayList<Rule> getInstantiatedCopies(Rule rule, List<Candidate> candidates,
                                        TreeMap<FunctionSymbol,FunctionSymbol> renamings) {
    ArrayList<Substitution> updates = getReplacementSubstitutions(rule.queryLeftSide(),
                                 rule.queryRightSide().freeReplaceables(), candidates);
    ArrayList<Rule> rulecopies = new ArrayList<Rule>();
    rulecopies.add(rule);
    applyAllUpdates(rulecopies, updates);
    renameAll(rulecopies, candidates, renamings);
    return rulecopies;
  }

  public TRS computeReplacementTRS(List<Candidate> candidates,
                                   TreeMap<FunctionSymbol,FunctionSymbol> renamings) {
    Alphabet newalf = _trs.queryAlphabet().add(renamings.values());
    TreeSet<String> newpriv = determinePrivate(renamings);
    ArrayList<Rule> newrules = new ArrayList<Rule>();
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      newrules.addAll(getInstantiatedCopies(_trs.queryRule(i), candidates, renamings));
    }
    return TrsFactory.createTrs(newalf, newrules, newpriv, false, 
      _trs.theoriesIncluded() ? TrsFactory.LCSTRS : TrsFactory.LCTRS);
  }

  public class TransformerProofObject implements ProofObject {
    private TRS _result;
    private List<Candidate> _candidates;
    private TreeMap<FunctionSymbol,FunctionSymbol> _renamings;

    /**
     * Creates the proof object:
     * - candidates is allowed to be null; in this case, the TRS does not satisfy the requirements
     * - candidates is allowed to be empty; in this case, no candidates for replacement were found
     * - candidates is allowed to be non-empty; in this case, the replacements can be done
     */
    private TransformerProofObject(List<Candidate> candidates,
                                   TreeMap<FunctionSymbol,FunctionSymbol> renamings, TRS result) {
      _candidates = candidates;
      _renamings = renamings;
      _result = result;
    }

    public Answer queryAnswer() {
      if (_candidates == null) return Answer.NO;
      else if (_candidates.size() == 0) return Answer.MAYBE;
      else return Answer.YES;
    }

    public TRS queryResultingTRS() { return _result; }

    public void justify(OutputModule module) {
      if (_candidates == null) {
        module.println("The TRS does not satisfy the conditions to apply the helper " +
          "function transformation.");
        return;
      }
      if (_candidates.size() == 0) {
        module.println("The helper function transformation was not applied: I could not " +
          "find any candidate positions to replace.");
        return;
      }
      // we actually did something!
      module.println("We observe that the TRS can be modified, without affecting " +
        "termination, in the following way:");
      module.startTable();
      for (Candidate cand : _candidates) {
        Term base = cand.below();
        Type t = base.queryType();
        for (int i = 1; i < cand.argument(); i++) {
          base.apply(TermFactory.createVar("x{" + i + "}", t.subtype(1)));
          t = t.subtype(2);
        }
        ArrayList<Term> subargs = new ArrayList<Term>();
        Type y = cand.main().queryType();
        for (int i = 1; i <= cand.numArgs(); i++) {
          subargs.add(TermFactory.createVar("y{" + i + "}", y.subtype(1)));
          y = y.subtype(2);
        }
        Term original = base.apply(cand.main().apply(subargs));
        Term replacement = base.apply(_renamings.get(cand.main()).apply(subargs));
        module.println("We replace all occurrences of %a by %a.", original, replacement);
      }
      module.endTable();
      module.print("This yields a(n) ");
      module.printTrs(_result);
    }
  }

  /**
   * This method checks if the helper function transformation can be applied, so as to generate a
   * TRS that is more convenient to analyse by static dependency pairs.
   */
  public TransformerProofObject transform() {
    if (!_applicable) return new TransformerProofObject(null, null, _trs);
    List<Candidate> candidates = getReplacementCandidates().stream()
                                    .filter(c -> checkCandidateSuitability(c)).toList();
    if (candidates.size() == 0) return new TransformerProofObject(candidates, null, _trs);
    TreeMap<FunctionSymbol,FunctionSymbol> copies = createCopies(candidates);
    TRS t = computeReplacementTRS(candidates, copies);
    return new TransformerProofObject(candidates, copies, t);
  }
}

