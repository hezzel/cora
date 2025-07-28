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

package cora.termination.dependency_pairs.processors.redpair;

import charlie.util.Pair;
import charlie.util.LookupMap;
import charlie.types.*;
import charlie.terms.*;
import charlie.trs.*;
import charlie.trs.TrsProperties.*;
import charlie.smt.*;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.config.Settings;
import cora.termination.reduction_pairs.*;
import cora.termination.dependency_pairs.Problem;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.processors.Processor;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.Map;

public class URWrtRedPairProcessor implements Processor {
  private ReductionPair _redpair;

  /** This technique can be disabled by runtime arguments. */
  public static String queryDisabledCode() { return "urwrt"; }

  /**
   * Creates a processor based on the given reduction pair. This is supposed to be a weakly
   * monotonic reduction pair that can handle disregarded arguments (though if it is a reduction
   * pair that regards all arguments, this processor may still work as essentially a combination of
   * unfiltered usable rules and a reduction pair).  It is allowed to be a reduction pair that can
   * only handle first-order systems (MSTRSs and LCTRSs).
   */
  public URWrtRedPairProcessor(ReductionPair rp) {
    _redpair = rp;
  }

  @Override
  public boolean isApplicable(Problem dpp) {
    return !Settings.isDisabled(queryDisabledCode()) &&
           dpp.isInnermost() &&
           dpp.getOriginalTRS().verifyProperties(Level.APPLICATIVE, Constrained.YES,
                       TypeLevel.SIMPLE, Lhs.PATTERN, Root.THEORY, FreshRight.CVARS);
  }

  /**
   * This translates an applicative term to a first-order term over the new signature, which is
   * being stored in map.  In doing so, amap is likely to be updated with the function symbols that
   * occur in t, and vmap with the variables that occur in t except for the variables of a theory
   * sort (these are all translated to themselves).
   *
   * The set lvar is given because theory terms will be returned unmodified if and only if all their
   * variables occur in lvar.
   */
  private Term translateTerm(AlphabetMap amap, TreeMap<Variable,Variable> vmap, Term t,
                             Set<Variable> lvar) {
    if (t.queryType().isBaseType() && t.queryType().isTheoryType() &&
        t.isTheoryTerm() && t.isFirstOrder()) {
      boolean ok = true;
      for (Variable x : t.vars()) {
        if (!lvar.contains(x)) { ok = false; break; }
      }
      if (ok) return t;
    }

    if (t.isVariable()) {
      Variable x = t.queryVariable();
      if (vmap.containsKey(x)) return vmap.get(x);
      Variable y = TermFactory.createVar(x.queryName(), amap.sortFor(x.queryType()));
      vmap.put(x, y);
      return y;
    }

    if (t.isFunctionalTerm()) {
      FunctionSymbol f = amap.getTranslation(t.queryRoot(), t.numberArguments());
      ArrayList<Term> args = new ArrayList<Term>(t.numberArguments());
      for (int i = 1; i <= t.numberArguments(); i++) {
        args.add(translateTerm(amap, vmap, t.queryArgument(i), lvar));
      }
      return f.apply(args);
    }
    
    // anything else should get filtered away, so is just mapped to a fresh function symbol
    return amap.generateBulletSymbol(t.queryType());
  }

  /** Translates a DP to a first-order DP over the new signature */
  private DP translateDP(AlphabetMap amap, DP dp) {
    TreeMap<Variable,Variable> vmap = new TreeMap<Variable,Variable>();
    Term lhs = translateTerm(amap, vmap, dp.lhs(), dp.lvars());
    Term rhs = translateTerm(amap, vmap, dp.rhs(), dp.lvars());
    return new DP(lhs, rhs, dp.constraint(), dp.lvars());
  }

  /**
   * Translates a rule to one or more first-order rules over the new signature, and adds them all
   * to the given storage list.
   */
  private void translateAndStoreRule(AlphabetMap amap, Rule rule, boolean constrained,
                                     ArrayList<Rule> storage) {
    TreeMap<Variable,Variable> vmap = new TreeMap<Variable,Variable>();
    Term lhs = rule.queryLeftSide();
    Term rhs = rule.queryRightSide();
    TreeSet<Variable> lvar = new TreeSet<Variable>(rule.queryLVars());
    for (int k = lhs.numberArguments() + 1; ; k++) {
      Term l = translateTerm(amap, vmap, lhs, lvar);
      Term r = translateTerm(amap, vmap, rhs, lvar);
      Rule rho = constrained
        ? TrsFactory.createRule(l, r, rule.queryConstraint(), TrsFactory.LCTRS)
        : TrsFactory.createRule(l, r, TrsFactory.MSTRS);
      storage.add(rho);

      Type sub = switch (lhs.queryType()) {
        case Arrow(Type in, Type out) -> in;
        case Base x -> null;
        case Product x -> null;
      };
      if (sub == null) break;
      Variable x = TermFactory.createVar("arg" + k, sub);
      lhs = lhs.apply(x);
      rhs = rhs.apply(x);
    }
  }

  private void storeFilteredCalculationRule(FunctionSymbol original, FunctionSymbol filtered,
                                            ArrayList<Rule> storage) {
    ArrayList<Term> args = new ArrayList<Term>(original.queryArity());
    Type t = original.queryType();
    for (int i = 1; t instanceof Arrow(Type in, Type out); i++) {
      args.add(TermFactory.createVar("x" + i, in));
      t = out;
    }
    Term left = filtered.apply(args);
    Variable right = TermFactory.createVar("y", t);
    Term constraint = TheoryFactory.createEquality(right, original.apply(args));
    storage.add(TrsFactory.createRule(left, right, constraint, TrsFactory.LCTRS));
  }

  /**
   * If rho = f(l1,...,lk) → r, this ensures that map contains a mapping f → x, where x is a BVar
   * that will be used to indicate usability of the symbol f.
   */
  private void storeUsableVariables(Rule rho, TreeMap<FunctionSymbol,BVar> map, SmtProblem smt) {
    FunctionSymbol f = rho.queryRoot();
    BVar x = map.get(f);
    if (x == null) {
      x = smt.createBooleanVariable("usable_{" + f.queryName() + "}");
      map.put(f, x);
    }
  }

  /** Creates an appropriate ordering requirement for a dependency pair */
  private OrderingRequirement createOrderingReq(DP dp) {
    return new OrderingRequirement(dp.lhs(), dp.rhs(), dp.constraint(),
                                   OrderingRequirement.Relation.Strict, dp.lvars());
  }

  /**
   * This function generates the first-order ordering problem with
   * * l ≻? r | φ for all translated dependency pairs l ⇒ r | φ
   *   (where ≻? indicates an "either" requirement)
   * * x_f ⇒ f(l1,...lk) ≽ r | φ for all translated rules f(l1,...,lk) → r | φ
   * The OrderingProblem is returned, and the boolean variables x_f for each symbol occurring in the
   * first-order TRS are stored in the conditions map.
   */
  private OrderingProblem makeOrderingProblem(Problem dpp, SmtProblem smt, ArgumentFilter filter,
                                              TreeMap<FunctionSymbol,BVar> conditions,
                                              AlphabetMap amap) {
    ArrayList<Rule> rules = new ArrayList<Rule>();
    ArrayList<DP> dps = new ArrayList<DP>();
    boolean constrained = dpp.getOriginalTRS().theoriesIncluded();

    for (DP dp : dpp.getDPList()) dps.add(translateDP(amap, dp));
    for (Rule rho : dpp.getRuleList()) translateAndStoreRule(amap, rho, constrained, rules);
    for (Pair<Pair<FunctionSymbol,Integer>,FunctionSymbol> p : amap.getAll()) {
      if (p.fst().fst().isTheorySymbol() && p.fst().snd() == p.fst().fst().queryArity()) {
        storeFilteredCalculationRule(p.fst().fst(), p.snd(), rules);
      }
    }
    for (Rule rho : rules) storeUsableVariables(rho, conditions, smt);

    TRS trs = TrsFactory.createTrs(amap.generateAlphabet(), rules,
                                   constrained ? TrsFactory.LCTRS : TrsFactory.MSTRS);

    OrderingProblem oprob = new OrderingProblem(trs, filter);
    for (int i = 0; i < dps.size(); i++) oprob.requireEither(createOrderingReq(dps.get(i)), i);
    for (Rule rho : rules) {
      oprob.requireConditionally(new OrderingRequirement(rho, OrderingRequirement.Relation.Weak),
                                 conditions.get(rho.queryRoot()));
    }
    return oprob;
  }
  
  /**
   * This function stores, into the given SmtProblem, the requirement that regards[f,i] <->
   * regards[f_n,i] for n ≥ i, where such a function symbol has been created.
   */
  private void storeEquivalentRegards(AlphabetMap amap, ArgumentFilter filter, SmtProblem smt) {
    ArrayList<Pair<Pair<FunctionSymbol,Integer>,FunctionSymbol>> all = amap.getAll();
    for (Pair<Pair<FunctionSymbol,Integer>,FunctionSymbol> p : all) {
      FunctionSymbol f = p.fst().fst();
      int n = p.fst().snd();
      FunctionSymbol g = p.snd();
      for (int i = 1; i <= n; i++) {
        smt.requireImplication(filter.regards(f, i), filter.regards(g, i));
        smt.requireImplication(filter.regards(g, i), filter.regards(f, i));
      }
    }
  }

  /**
   * This function stores in smt the requirements on the regards function for the usable_f variables
   * to correctly indicate when a function symbol is usable.  This also stores the reuqirements that
   * ⊥ is not a usable symbol.
   *
   * Note that we store one-way implications; for example, for a rule f(x) → g(x, h(3))
   * we store usable_f ∧ regards[g,2] → usable_h, not an if and only if.  Thus, false positives
   * on usability are allowed; the reduction pair is allowed to orient more rules than needed if it
   * wants to.
   */
  private void storeRegardsRequirements(AlphabetMap amap, Problem dpp, ArgumentFilter filter,
                                        TreeMap<FunctionSymbol,BVar> conditions, SmtProblem smt) {
    ArrayList<Constraint> sofar = new ArrayList<Constraint>();
    for (DP dp : dpp.getDPList()) {
      addUsableRequirements(dp.rhs(), sofar, filter, conditions, amap, dp.lvars(), smt);
    }
    for (Rule rho : dpp.getRuleList()) {
      FunctionSymbol f = rho.queryRoot();
      int k = rho.queryLeftSide().numberArguments();
      Term rhs = rho.queryRightSide();
      for (int n = k; n <= f.queryArity(); n++) {
        FunctionSymbol g = amap.getTranslation(f, n);
        BVar x = conditions.get(g);
        conditions.put(g, null);  // we don't want unnecessary clauses usable_f → usable_f, which we
                                  // would get a lot of (from recursive rules) without this
        sofar.add(x.negate());
        Set<Variable> lvar = new TreeSet<Variable>(rho.queryLVars());
        addUsableRequirements(rhs, sofar, filter, conditions, amap, lvar, smt);
        conditions.put(g, x);
        sofar.clear();
        if (rhs.queryType() instanceof Arrow(Type in, Type out)) {
          rhs = rhs.apply(TermFactory.createVar(in));
        }
      }
    }
  }

  /**
   * This function stores, into the given SmtProblem, clauses [sofar] ∨ ¬regards[f1,i1] ∨...∨
   * ¬regards[fn,in] or [sofar] ∨ ¬regards[f1,i1] ∨...∨ ¬regards[fn,in] ∨ usable_g, so that:
   * - for every occurrence of a subterm g(...) of term such that there is a usability condition
   *   variable usable_g, this stores: sofar ∨ [this subterm is not regarded] ∨ usable_g
   * - for every occurrence of a variable application x(...) with at least one argument, this
   *   stores: sofar ∨ [this subterm is not regarded]
   */
  private void addUsableRequirements(Term term, ArrayList<Constraint> sofar, ArgumentFilter filter,
                                     TreeMap<FunctionSymbol,BVar> conditions,
                                     AlphabetMap amap, Set<Variable> lvar, SmtProblem smt) {
    if (term.isVariable()) return;
    
    // don't add requirements for theory terms that are going to get normalised to a value
    if (term.queryType().isBaseType() && term.queryType().isTheoryType() &&
        term.isTheoryTerm() && term.isFirstOrder()) {
      boolean ok = true;
      for (Variable x : term.vars()) {
        if (!lvar.contains(x)) { ok = false; break; }
      }
      if (ok) return;
    }

    if (term.isFunctionalTerm()) {
      FunctionSymbol f = term.queryRoot();
      int n = term.numberArguments();
      FunctionSymbol g = amap.getTranslation(f, n);
      BVar bvar = conditions.get(g);
      if (bvar != null) {
        sofar.add(bvar);
        smt.require(SmtFactory.createDisjunction(sofar));
        sofar.remove(sofar.size()-1);
      }
      int k = term.numberArguments();
      for (int i = 1; i <= k; i++) {
        sofar.add(filter.regards(g, i).negate());
        addUsableRequirements(term.queryArgument(i), sofar, filter, conditions, amap, lvar, smt);
        sofar.remove(sofar.size()-1);
      }
    }

    // everything else is illegal -- this really should only be varterms anyway
    else {
      smt.require(SmtFactory.createDisjunction(sofar));
    }
  }

  /**
   * This function stores the requirement that for rules f(l1,...,lk) → g(r1,...,rp) of higher type,
   * for k < i ≤ n := arity(f), we have: if (f,n) is usable, and i ∉ regards[f], then p + (i-k) ∉
   * regards[g].
   */
  private void storeHORuleRegardsRequirement(AlphabetMap amap, Problem dpp, ArgumentFilter filter,
                                             TreeMap<FunctionSymbol,BVar> conditions,
                                             SmtProblem smt) {
    for (Rule rule : dpp.getRuleList()) {
      Term lhs = rule.queryLeftSide(), rhs = rule.queryRightSide();
      if (rhs.queryType().isBaseType() || !rhs.isFunctionalTerm()) continue;
      FunctionSymbol f = lhs.queryRoot(), g = rhs.queryRoot();
      int k = rule.queryLeftSide().numberArguments(), p = rhs.numberArguments();
      for (int n = k + 1; n <= f.queryArity(); n++) {
        FunctionSymbol fn = amap.getTranslation(f, n);
        for (int i = k + 1; i <= n; i++) {
          ArrayList<Constraint> parts = new ArrayList<Constraint>(3);
          parts.add(conditions.get(fn).negate());
          parts.add(filter.regards(f, i));
          parts.add(filter.regards(g, p + i - k).negate());
          smt.require(SmtFactory.createDisjunction(parts));
        }
      }
    }
  }
  
  @Override
  public ProcessorProofObject processDPP(Problem dpp) {
    SmtProblem smt = new SmtProblem();
    ArgumentFilter filter = new ArgumentFilter(smt);
    TreeMap<FunctionSymbol,BVar> conditions = new TreeMap<FunctionSymbol,BVar>();
    AlphabetMap amap = new AlphabetMap();
    
    OrderingProblem oprob = makeOrderingProblem(dpp, smt, filter, conditions, amap);
    storeEquivalentRegards(amap, filter, smt);
    storeRegardsRequirements(amap, dpp, filter, conditions, smt);
    storeHORuleRegardsRequirement(amap, dpp, filter, conditions, smt);

    if (!_redpair.isApplicable(oprob)) return new WrtProofObject(dpp, _redpair.queryName());
    ReductionPairProofObject ob = _redpair.solve(oprob, smt);
    if (ob.queryAnswer() == ProofObject.Answer.YES) {
      TreeSet<Integer> remove = new TreeSet<Integer>();
      List<DP> dps = dpp.getDPList();
      for (int i = 0; i < dps.size(); i++) {
        if (ob.isStrictlyOriented(i)) remove.add(i);
      }
      Problem altered = dpp.removeDPs(remove, true);
      return new WrtProofObject(dpp, altered, _redpair.queryName(), ob);
    }   
    else return new WrtProofObject(dpp, _redpair.queryName(), ob);
  }
}

class WrtProofObject extends ProcessorProofObject {
  private String _name;
  private ReductionPairProofObject _rpob;
  
  /** Used for a failed proof where the method wasn't even applicable */
  public WrtProofObject(Problem input, String name) {
    super(input);
    _name = name;
    _rpob = null;
  }

  /** Used for a failed proof where the method was nevertheless applicable. */
  public WrtProofObject(Problem input, String name, ReductionPairProofObject ob) {
    super(input);
    _name = name;
    _rpob = ob;
  }

  /** Used for a successful proof. */
  public WrtProofObject(Problem input, Problem output, String name, ReductionPairProofObject ob) {
    super(input, output);
    _name = name;
    _rpob = ob;
  }

  public String queryProcessorName() {
    return "Usable rules with respect to an argument wiltering [with " + _name + "]";
  }

  public void justify(OutputModule module) {
    if (_rpob == null) {
      module.println("This reduction pair is not applicable to the generated ordering problem.");
      return;
    }
    _rpob.justify(module);
  }
}

