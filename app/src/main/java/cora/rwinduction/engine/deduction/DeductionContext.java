/**************************************************************************************************
 Copyright 2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rwinduction.engine.deduction;

import java.util.*;
import charlie.util.Pair;
import charlie.terms.position.Position;
import charlie.terms.position.ArgumentPos;
import charlie.terms.replaceable.Renaming;
import charlie.terms.*;
import charlie.printer.Printer;
import charlie.printer.PrinterFactory;
import cora.config.Settings;
import cora.io.OutputModule;
import cora.rwinduction.engine.*;

/**
 * This class handles the CONTEXT command, which is essentially a generalisation of the
 * SEMICONSTRUCTOR rule combined with DELETION steps on obviously-equal result equations.
 *
 * Its purpose is to split an equation C[s1,...,sn] = C[t1,...,tn] | φ into the n equations
 * si = ti | φ.  If the context above each si consists entirely of constructors or partially
 * applied function symbols, then this step is complete.
 *
 * We also immediately handle SEMICONSTRUCTOR as a special case.
 */
public final class DeductionContext extends DeductionStep {
  private boolean _complete;
  private boolean _isBasic; // holds if C is f([],...,[]) for f a symbol or variable
  private ArrayList<Position> _positions;
  private ArrayList<Pair<Term,Term>> _subtermsAtPositions;

  /** Create a context command for the given positions. */
  private DeductionContext(ProofState state, ProofContext context, boolean complete,
                           ArrayList<Position> posses, ArrayList<Pair<Term,Term>> subterms) {
    super(state, context);
    _complete = complete;
    _isBasic = false;
    _positions = posses;
    _subtermsAtPositions = subterms;
  }

  /**
   * Create a context command for the immediate subpositions of the root.  If this step is complete,
   * it is an instance of SEMICONSTRUCTOR, and we remember that for use in printing to the user.
   */
  private DeductionContext(ProofState state, ProofContext context, boolean complete) {
    super(state, context);
    _complete = complete;
    _isBasic = true;
    _positions = new ArrayList<Position>();
    _subtermsAtPositions = new ArrayList<Pair<Term,Term>>();
    Term left = state.getTopEquation().getLhs();
    Term right = state.getTopEquation().getRhs();
    for (int i = 1; i <= left.numberArguments(); i++) {
      _positions.add(new ArgumentPos(i, Position.empty));
      _subtermsAtPositions.add(new Pair<Term,Term>(left.queryArgument(i), right.queryArgument(i)));
    }
  }

  /**
   * This creates the context step for C[s1,...,sn] = C[t1,...,tn], where the open places in the
   * context occur at the given positions.
   *
   * This means that the positions must be:
   * - parallel to each other (none of them is above another)
   * - not partial
   * - non-empty (there is at least one), otherwise we should just be using DELETE
   * - not the empty position, otherwise the step has no effect
   */
  public static DeductionContext createStep(PartialProof proof,
                                            Optional<OutputModule> module,
                                            List<Position> positions) {
    if (positions.size() == 0) {
      module.ifPresent(o -> o.println("At least one position should be given to CONTEXT."));
      return null;
    }
    if (positions.size() == 1 && positions.get(0).isEmpty()) {
      module.ifPresent(o -> o.println("Cannot use CONTEXT with the empty position: " +
        "the step would have no effect."));
      return null;
    }

    EquationContext ec = getTopEquation(proof.getProofState(), module);
    ArrayList<Pair<Integer,Position>> posses = getSorted(positions);
    TreeMap<Integer,Pair<Term,Term>> info = new TreeMap<Integer,Pair<Term,Term>>();
    int chk = checkPositions(ec.getLhs(), ec.getRhs(), ec.getRenaming(), posses, module, info,
                             new LinkedList<Integer>(), proof.getContext());
    if (chk == 0) return null;
    ArrayList<Pair<Term,Term>> pairs = new ArrayList<Pair<Term,Term>>();
    for (int i = 0; i < posses.size(); i++) pairs.add(info.get(i));
    return new DeductionContext(proof.getProofState(), proof.getContext(), chk == 2,
                                new ArrayList<Position>(positions), pairs);
  }

  /**
   * This returns a sorted variant of the given position list, using the first element of the pair
   * to indicate each position's original placement in the positions list.
   */
  private static ArrayList<Pair<Integer,Position>> getSorted(List<Position> positions) {
    ArrayList<Pair<Integer,Position>> ret = new ArrayList<Pair<Integer,Position>>();
    int i = 0;
    for (Position pos : positions) ret.add(new Pair<Integer,Position>(i++, pos));
    Collections.sort(ret, new Comparator<Pair<Integer,Position>>() {
      public int compare(Pair<Integer,Position> pair1, Pair<Integer,Position> pair2) {
        return pair1.snd().compareTo(pair2.snd());
      }
    });
    return ret;
  }

  /**
   * This goes through left and right, and checks that they both have all the positions in the
   * given (lexicographically ordered) positions list, and the context where each of those positions
   * is replaced by a box is the same for both left and right.
   * If this is not the case, then 0 is returned.
   * If it is the case, then all the pairs posindex → <leftatpos,rightatpos> are added to info, and
   * either 1 or 2 is returned: 2 if all subterms ABOVE a box have the form f(s1,...sn) with
   * n < ar(f), and 1 if there is some subterm where this is not the case.
   *
   * It is required that the positions are all parallel and full positions.  If this is not the
   * case, then an error message is printed and 0 is returned too.  They are expected to be in
   * lexicographical ordering, as this function should only be called from the createStep function,
   * which performs a sort first.
   *
   * Whenever 0 is returned, an error message is printed on the given output module.
   */
  private static int checkPositions(Term left, Term right, Renaming renaming,
                                    List<Pair<Integer,Position>> positions, // (posindex, pos)
                                    Optional<OutputModule> module,
                                    TreeMap<Integer,Pair<Term,Term>> info,
                                    LinkedList<Integer> curpos, ProofContext context) {
    if (!checkPositionConditions(left, right, renaming, positions, module, curpos)) return 0;
    // base case: we are given the root position
    if (positions.size() == 1 && positions.get(0).snd().isEmpty()) {
      info.put(positions.get(0).fst(), new Pair<Term,Term>(left, right));
      return 2;
    }
    // go through all the subterms, and either check their positions or equality
    int best = 2;
    int k = 0;
    ArrayList<Pair<Integer,Position>> subposses = new ArrayList<Pair<Integer,Position>>();
    for (int i = 1; i <= left.numberArguments(); i++) {
      subposses.clear();
      for (; k < positions.size() && positions.get(k).snd().queryHead() == i; k++) {
        subposses.add(new Pair<Integer,Position>(positions.get(k).fst(),
                                                 positions.get(k).snd().queryTail()));
      }
      if (subposses.size() == 0) {
        if (!left.queryArgument(i).equals(right.queryArgument(i))) {
          Position p = Position.of(curpos, new ArgumentPos(i, Position.empty));
          module.ifPresent(o -> o.println("The subterms at position %a are not the same.", p));
          return 0;
        }
      }
      else {
        curpos.add(i);
        int result = checkPositions(left.queryArgument(i), right.queryArgument(i), renaming,
                                    subposses, module, info, curpos, context);
        curpos.removeLast();
        if (result == 0) return 0;
        if (result == 1) best = 1;
      }
    }
    // if we're still complete, check if we can keep that
    if (best == 2) {
      if (!left.isFunctionalTerm() ||
          left.numberArguments() >= context.queryRuleArity(left.queryRoot())) best = 1;
    }
    return best;
  }

  /**
   * Helper function for checkPositions: this handles all the possible failure cases: if there is an
   * immediate problem (at the top terms left and right) then this gives an appropriate error
   * message on the output module, and returns false.  If there is no immediately obvious problem,
   * it returns true, allowing checkPositions to descend into the arguments.
   */
  private static boolean checkPositionConditions(Term left, Term right, Renaming renaming,
        List<Pair<Integer,Position>> positions, Optional<OutputModule> module,
        LinkedList<Integer> curpos) {
    // empty positions are fine; partial positions are not
    if (positions.size() == 1) {
      if (positions.get(0).snd().isEmpty()) return true;
      if (positions.get(0).snd().isFinal()) {
        module.ifPresent(o -> o.println("The context rule cannot be applied with a partial " +
          "position %a.", Position.of(curpos, positions.get(0).snd())));
        return false;
      }
    }
    // if we are not given an empty position, both terms must have the same outer shape
    if (!left.queryHead().equals(right.queryHead())) {
      module.ifPresent(o -> o.println("The context rule is not applicable, since the subterms " +
        "at position %a have different head terms (%a and %a).", Position.of(curpos),
        Printer.makePrintable(left.queryHead(), renaming),
        Printer.makePrintable(right.queryHead(), renaming)));
      return false;
    }
    int n = left.numberArguments();
    if (n != right.numberArguments()) {
      module.ifPresent(o -> o.println("The context rule is not applicable, since the subterms " +
        "at position %a have a different number of arguments.", Position.of(curpos)));
      return false;
    }
    // the positions must all be argument positions, supplied in the right order, and in range
    for (Pair<Integer,Position> pair : positions) {
      Position pos = pair.snd();
      if (pos instanceof ArgumentPos(int index, Position tail)) {
        if (index > n) {
          module.ifPresent(o -> o.println("There is no position %a: the subterm at position %a %a!",
            Position.of(curpos, pos), Position.of(curpos),
            n == 0 ? "has no arguments" : "only has " + n + "arguments"));
          return false;
        }
      }
      else if (pos.isFinal()) {
        module.ifPresent(o -> o.println("The given positions are not parallel."));
        return false;
      }
      else {
        module.ifPresent(o -> o.println("Unexpected position: %a.  This does not represent a " +
          "position in a fully applicative term.", Position.of(curpos, pos)));
        return false;
      }
    }
    return true;
  }

  /**
   * This creates a semiconstructor step where the left- and right-hand side should both be of the
   * same shape f(s1,...,sn), with the same (variable or function symbol) f and same n; it creates
   * the context step for positions 1...n.
   */
  public static DeductionContext createStep(PartialProof proof,
                                            Optional<OutputModule> module,
                                            boolean shouldBeComplete) {
    ProofState state = proof.getProofState();
    EquationContext ec = DeductionStep.getTopEquation(state, module);
    if (ec == null) return null;

    String name = shouldBeComplete ? "semiconstructor" : "context";

    if (!ec.getLhs().queryHead().equals(ec.getRhs().queryHead())) {
      module.ifPresent(o -> o.println("The " + name + " rule cannot be applied, because the " +
        "two sides of the equation do not have the same head."));
      return null;
    }
    if (ec.getLhs().numberArguments() != ec.getRhs().numberArguments()) {
      module.ifPresent(o -> o.println("The " + name + " rule cannot be applied, because the " +
        "two sides of the equation do not have the same number of arguments."));
      return null;
    }

    boolean isComplete = checkCompleteness(ec.getEquation(), proof.getContext());
    if (shouldBeComplete && !isComplete) {
      module.ifPresent(o -> o.println("The semiconstructor rule can only be applied if both " +
        "sides of the equation have a form f s1 ... sn, with f a function symbol and n < ar(f).  " +
        "(Use \"context\" for the more general form, which does, however, lose completeness in " +
        "this case.)"));
      return null;
    }

    return new DeductionContext(state, proof.getContext(), isComplete);
  }
 
  /**
   * Helper function for createStep: this checks if we really have an application of SEMICONSTRUCTOR
   * or one that we will consider CONTEXT.
   */
  private static boolean checkCompleteness(Equation equation, ProofContext pcontext) {
    Term left = equation.getLhs();
    if (!left.isFunctionalTerm()) return false;
    FunctionSymbol f = left.queryRoot();
    int n = left.numberArguments();
    int k = pcontext.queryRuleArity(f);
    return n < k;
  }

  /** 
   * This function edits the two lists, posses and pairs, by adding p into posses and (s|_p,t|_p)
   * into pairs, where p is any of the parallel positions so that s|_p and t|_p are distinct and
   * the terms without the given positions are maximal semi-constructor contexts.
   *
   * That is, we find all positions p, in lexicographical ordering, so that the positions above p
   * have the same semi-constructor shape in s and t, and so that s|_p != t|_p, and s|_p and t|_p
   * do not themselves have the same semi-constructor shape.
   *
   * We only consider argument contexts, not head contexts.
   */
  public static void storeDifferences(Term s, Term t, ProofContext context, ArrayList<Position>
                                      posses, ArrayList<Pair<Term,Term>> pairs) {
    // If the heads are not the same, we clearly are not part of a context surrounding a difference
    // (as we only consider argument contexts, not head contexts), so store [(ε,(s,t))].
    if (!s.queryHead().equals(t.queryHead()) || s.numberArguments() != t.numberArguments()) {
      posses.add(Position.empty);
      pairs.add(new Pair<Term,Term>(s,t));
      return;
    }
    // similarly, if we're not a semi-constructor context, we must return either [(ε,(s,t))] (if
    // s and t are unequal) or [] (if they are equal)
    if (!s.isFunctionalTerm() || s.numberArguments() >= context.queryRuleArity(s.queryRoot())) {
      if (!s.equals(t)) {
        posses.add(Position.empty);
        pairs.add(new Pair<Term,Term>(s,t));
      }
      return;
    }
    // otherwise, recursively descend into the children and detect differences there
    int n = s.numberArguments();
    int k = posses.size();
    for (int i = 1; i <= n; i++) {
      storeDifferences(s.queryArgument(i), t.queryArgument(i), context, posses, pairs);
      if (posses.size() > k) {
        for (int j = k; j < posses.size(); j++) {
          // update the position to be in the current terms, not the subterms
          posses.set(j, new ArgumentPos(i, posses.get(j)));
        }
        k = posses.size();
      }
    }
  }

  /**
   * This returns whether this instance of the CONTEXT step is complete.
   */
  public boolean isComplete() {
    return _complete;
  }

  @Override
  public boolean verify(Optional<OutputModule> module) {
    return true;
  }

  @Override
  public ProofState tryApply(Optional<OutputModule> module) {
    ArrayList<EquationContext> neweqs = new ArrayList<EquationContext>();
    Term constr = _equ.getEquation().getConstraint();
    int index = _state.getLastUsedIndex();
    for (int i = _subtermsAtPositions.size()-1; i >= 0; i--) {
      Equation newequation = new Equation(_subtermsAtPositions.get(i).fst(),
                                          _subtermsAtPositions.get(i).snd(),
                                          constr);
      index++;
      neweqs.add(_equ.replace(newequation, index));
    }
    ProofState state = _state;
    if (!_complete) state = state.setIncomplete(_equ.getIndex());
    return state.replaceTopEquation(neweqs);
  }

  @Override
  public String commandDescription() {
    if (_isBasic) {
      if (_complete) return "semiconstructor";
      else return "context";
    }
    Printer printer = PrinterFactory.createParseablePrinter(_pcontext.getTRS());
    printer.add("context");
    for (Position pos : _positions) {
      printer.add(" ");
      printer.add(pos);
    }
    return printer.toString();
  }

  @Override
  public void explain(OutputModule module) {
    if (!_complete || !_isBasic) {
      module.println("We apply CONTEXT to %a, splitting the immediate arguments into " +
        "separate equations.%a", _equ.getName(),
        _state.getIncompleteEquations().contains(_equ.getIndex()) ? "" :
        _complete ? "  We preserve the completeness flag." : "  We lose the completeness flag.");
      return;
    }
    FunctionSymbol f = _equ.getEquation().getLhs().queryRoot();
    if (_pcontext.getTRS().isDefined(f) || f.toCalculationSymbol() != null) {
      module.println("We apply SEMICONSTRUCTOR to %a, since the rule arity of %a is %a and only " +
        "%a arguments are present.", _equ.getName(), f, _pcontext.queryRuleArity(f),
        _equ.getEquation().getLhs().numberArguments());
    }
    else module.println("We apply SEMICONSTRUCTOR to %a since %a is a constructor symbol.",
      _equ.getName(), f.queryName());
  }
}

