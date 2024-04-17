package cora.termination.dependency_pairs;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.TreeMap;
import java.util.Map;

import charlie.exceptions.NotYetImplementedError;
import charlie.util.Pair;
import cora.io.OutputModule;
import cora.io.ProofObject;
import charlie.types.*;
import charlie.terms.*;
import charlie.smt.*;
import charlie.trs.TRS;
import cora.config.Settings;

public class AccessibilityChecker {
  private SmtProblem _problem;
  private TreeMap<String,IVar> _sortVariables;
  private TRS _trs;
  private String _result;

  public AccessibilityChecker(TRS trs) {
    _problem = new SmtProblem();
    _sortVariables = new TreeMap<String,IVar>();
    _trs = trs;
  }

  private IVar getSortVariable(String sort) {
    if (!_sortVariables.containsKey(sort)) {
      _sortVariables.put(sort, _problem.createIntegerVariable());
    }
    return _sortVariables.get(sort);
  }

  /** Returns a constraint modelling ι ≽+ σ */
  private Constraint posGeq(Base iota, Type sigma) {
    switch (sigma) {
      case Base(String name):
        return SmtFactory.createGeq(getSortVariable(iota.toString()), getSortVariable(name));
      case Arrow(Type left, Type right):
        return SmtFactory.createConjunction(minGre(iota, left), posGeq(iota, right));
      default:
        throw new NotYetImplementedError("accessibility has not yet been defined for product types");
    }
  }

  /** Returns a constraint modelling ι ≻- σ */
  private Constraint minGre(Base iota, Type sigma) {
    switch (sigma) {
      case Base(String name):
        return SmtFactory.createGreater(getSortVariable(iota.toString()), getSortVariable(name));
      case Arrow(Type left, Type right):
        return SmtFactory.createConjunction(posGeq(iota, left), minGre(iota, right));
      default:
        throw new NotYetImplementedError("accessibility has not yet been defined for product types");
    }
  }

  /** Returns whether i ∈ Acc(f) */
  private Constraint accArg(int i, FunctionSymbol f) {
    Type type = f.queryType();
    for (int j = 1; j < i; j++) {
      if (!type.isArrowType()) {
        throw new Error("Calling accArg(" + i + ", " + f + "), but f has type " + type + ".");
      }
      type = type.subtype(2);
    }
    Type argtype = type.subtype(1);
    Type output = type.queryOutputType();
    if (output.isBaseType()) return posGeq((Base)output, argtype);
    throw new NotYetImplementedError("Calling accArg with output type " + output);
  }

  /** Generates the requirements that all variables in s are at accessible possitions */
  private void requireAllVarsAcc(Term s) {
    // a variable is definitely accessible in itself
    if (s.isVariable()) return;
    // abstractions are not supported, and non-patterns are not okay!
    if (!s.isFunctionalTerm()) { _problem.require(SmtFactory.createValue(false)); return; }
    // okay, get the output type and argument types
    FunctionSymbol f = s.queryRoot();
    Type type = f.queryType();
    ArrayList<Type> argtypes = new ArrayList<Type>();
    while (type instanceof Arrow(Type input, Type output)) {
      argtypes.add(input);
      type = output;
    }
    if (!type.isBaseType()) {
      throw new NotYetImplementedError("allVarsAcc with term " + s + " with output type " + type);
    }
    Base output = (Base)type;
    if (argtypes.size() < s.numberArguments()) {
      throw new Error("allVarsAcc; this shouldn't happen due to type restrictions");
    }
    // check all the arguments with variables in them!
    for (int i = 1; i <= s.numberArguments(); i++) {
      Term arg = s.queryArgument(i);
      if (arg.freeReplaceables().size() == 0) continue;
      Type argtype = argtypes.get(i-1);
      _problem.require(posGeq(output, argtype));
      requireAllVarsAcc(arg);
    }
  }

  private void generateTrsConstraints() {
    for (int i = 0; i < _trs.queryRuleCount(); i++) {
      Term left = _trs.queryRule(i).queryLeftSide();
      for (int j = 1; j <= left.numberArguments(); j++) {
        requireAllVarsAcc(left.queryArgument(j));
      }
    }
  }

  /**
   * Only for unit testing: returns the constraint indicating that all variables in the lhs of a
   * rule are accessible in an immediate argument of the lhs.
   */
  String printTrsConstraints() {
    generateTrsConstraints();
    String ret = _problem.toString();
    _problem.clear();
    return ret;
  }

  private class AccessibilityProofObject implements ProofObject {
    private ArrayList<Pair<String,Integer>> _sorts;

    private AccessibilityProofObject(Valuation solution) {
      _sorts = new ArrayList<Pair<String,Integer>>();
      _sortVariables.forEach( (x, v) -> {
        _sorts.add(new Pair<String,Integer>(x, solution.queryAssignment(v)));
      });
      Collections.sort(_sorts, new Comparator<Pair<String,Integer>>() {
        public int compare(Pair<String,Integer> p1, Pair<String,Integer> p2) {
          return p2.snd() - p1.snd();
        }
      });
    }

    private AccessibilityProofObject() {
      _sorts = null;
    }

    public Boolean queryAnswer() { return _sorts != null; }

    public void justify(OutputModule module) {
      if (_sorts == null) {
        module.println("The system does not satisfy the preconditions to apply static " +
                       "dependency pairs: it is not accessible function passing.");
        return;
      }
      
      module.print("The system is accessible function passing by ");

      if (_sorts.size() == 0 ||
          _sorts.get(0).snd().equals(_sorts.get(_sorts.size()-1).snd())) {
        module.println("a sort ordering that equates all sorts.");
        return;
      }

      module.print("a sort ordering with %a", _sorts.get(0).fst());
      for (int i = 1; i < _sorts.size(); i++) {
        if (_sorts.get(i).snd() < _sorts.get(i-1).snd()) module.print(" ≻ ");
        else module.print(" = ");
        module.print("%a", _sorts.get(i).fst());
      }
      module.println(".");
    }
  }

  public ProofObject checkAccessibility() {
    generateTrsConstraints();
    switch (Settings.smtSolver.checkSatisfiability(_problem)) {
      case SmtSolver.Answer.YES(Valuation solution):
        return new AccessibilityProofObject(solution);
      default:
        return new AccessibilityProofObject();
    }
  }

  public String querySortOrdering() {
    return _result;
  }
}
