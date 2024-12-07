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

package cora.termination.dependency_pairs;

import charlie.util.FixedList;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import charlie.trs.Rule;
import cora.io.OutputModule;
import cora.io.OutputModuleAdapter;
import cora.io.ProofObject;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;

/**
 * The DP Framework gradually builds a proof object, that shows how the initial DP problem is
 * stepwise simplified.
 */
class DPProofObject implements ProofObject {
  private ProofObject _accessibilityCheck;
  private Problem _initialProblem;
  private ArrayList<ProcessorProofObject> _processorProofs;
  private Answer _answer;
  private Problem _failure;

  /**
   * This starts up a ProofObject for a system where the static dependency pair method is
   * *not* applicable, for instance because it is not accessible function passing.  The given
   * proof object contains the argument why it is not applicable.
   *
   * Note that, after using this constructor, no further calls of addProcessorProof may be done on
   * it.  Similarly, the response and failure reason do not need to be set.  (There is relatively
   * little error checking on this, because these functions are all package-private.)
   */
  DPProofObject(ProofObject accessibility) {
    _accessibilityCheck = accessibility;
    _initialProblem = null;
    _processorProofs = new ArrayList<ProcessorProofObject>();
    _answer = Answer.MAYBE;
    _failure = null;
  }

  /**
   * This starts up a ProofObject for a system where the static dependency pair method *is*
   * applicable, with the given initial DP problem (that should correspond to DP(R)).
   * After the constructor is called, addProcessorProof should be called with every simplification
   * until either the proof is complete (in which case setTerminating or setNonTerminating() should
   * be called), or the proof is abandoned (in which case setFailedProof should be called, or the
   * default value of MAYBE is returned by queryAnswer).
   */
  DPProofObject(ProofObject accessibility, Problem initial) {
    _accessibilityCheck = accessibility;
    _initialProblem = initial;
    _processorProofs = new ArrayList<ProcessorProofObject>();
    _answer = Answer.MAYBE;
    _failure = null;
  }

  /**
   * This marks the proof as complete, with a successful termination proof.
   * Package-private because this should only be done by the DP Framework constructing this object.
   */
  void setTerminating() { _answer = Answer.YES; }

  /**
   * This marks the proof as complete, with a successful non-termination proof.
   * Package-private because this should only be done by the DP Framework constructing this object.
  */
  void setNonTerminating() { _answer = Answer.NO; }

  /**
   * This marks the proof as abandoned, with the given DP Problem being unsimplifable by current
   * techniques.
   * Package-private because this should only be done by the DP Framework constructing this object.
   */
  void setFailedProof(Problem problem) {
    _failure = problem;
    _answer = Answer.MAYBE;
  }

  /**
   * This adds a proof from a processor.
   * Package-private because this should only be done by the DP Framework constructing this object.
   */
  void addProcessorProof(ProcessorProofObject procproof) {
    _processorProofs.add(procproof);
  }

  /**
   * Returns the termination status we have thus far stored.
   * If neither setTerminating() nor setNonTerminating() has been called, this yields MAYBE.
   * Otherwise it returns YES or NO respectively.
   */
  public Answer queryAnswer() {
    return _answer;
  }

  /** This prints the full proof to output. */
  public void justify(OutputModule module) {
    module = new OutputModuleWithDependencyPairs(module);
    _accessibilityCheck.justify(module);
    if (_initialProblem == null) return;

    // in the functions called by this, we will preserve the following property: a DP problem has
    // been seen before if and only if its name is stored in names; if it this is the case, then
    // the names of its DPs and rules are stored in pnames and rnames respectively
    HashMap<Problem,String> names = new HashMap<Problem,String>();
    HashMap<List<DP>,String> pnames = new HashMap<List<DP>,String>();
    HashMap<FixedList<Rule>,String> rnames = new HashMap<FixedList<Rule>,String>();
    rnames.put(_initialProblem.getOriginalTRS().queryRules(), "R");

    justifyStart(module, names, pnames, rnames);
    for (ProcessorProofObject po : _processorProofs) {
      justifyProcessor(module, po, names, pnames, rnames);
    }
    justifyEnd(module, names, pnames, rnames);
  }

  /**
   * Helper function for justify: if the DP problem does not already exist in the given mapping,
   * then we store it and return true.  If it does exist, then nothing is done and we return false.
   */
  private boolean storeDPP(Problem prob, HashMap<Problem,String> names) {
    if (names.containsKey(prob)) return false;
    names.put(prob, "D" + (names.size() + 1));
    return true;
  }

  /**
   * Helper function for justify: if the DP list of the given problem does not already exist in the
   * mapping of known DP lists, then we store it, and return true.  If it does exist, then nothing
   * is done and we return false.
   */
  private boolean storeDPList(Problem prob, HashMap<List<DP>,String> pnames) {
    if (pnames.containsKey(prob.getDPList())) return false;
    pnames.put(prob.getDPList(), "P" + (pnames.size() + 1));
    return true;
  }

  /**
   * Helper function for justify: if the rules list of the given problem does not already exist in
   * the mapping of known rule lists (and is not empty), then we store it, and return true.  If it
   * does exist, then nothing is done and we return false.
   */
  private boolean storeRuleList(Problem prob, HashMap<FixedList<Rule>,String> rnames) {
    if (prob.getRuleList().isEmpty()) return false;
    if (rnames.containsKey(prob.getRuleList())) return false;
    rnames.put(prob.getRuleList(), "R" + (rnames.size() + 1));
    return true;
  }

  /**
   * Helper function for justify: this prints a description of a DP problem, where the set of
   * dependency pairs and the set of variables are named (they are not explained in this function).
   */
  private void printDPP(OutputModule module, Problem problem, HashMap<Problem,String> probnames,
                        HashMap<List<DP>,String> pnames, HashMap<FixedList<Rule>,String> rnames) {
    String name = probnames.get(problem);
    String pname = pnames.get(problem.getDPList());
    String rules = problem.getRuleList().isEmpty() ? "%{emptyset}"
                                                   : rnames.get(problem.getRuleList());
    String extrarules = problem.hasExtraRules() ? " %{union} R_?" : "";
    String innermost = problem.isInnermost() ? "i" : "f";
    String termination = switch (problem.queryTerminationStatus()) {
      case Computable -> "c";
      case Terminating -> "t";
      case Arbitrary -> "a";
    };
    module.print("%a = (%a, " + rules + extrarules + ", %a, %a)",
      name, pname, innermost, termination);
  }

  /** This prints the DP list of the given problem to the output module, including a name. */
  private void printDPs(OutputModule module, Problem problem, String name) {
    module.startTable();
    int counter = 0;
    for (int i = 0; i < problem.getDPList().size(); i++) {
      DP dp = problem.getDPList().get(i);
      module.nextColumn(counter == 0 ? name + "." : "");
      counter++;
      module.nextColumn("(%a)", counter);
      module.nextColumn("%a", makeDPObject(dp, module));
      if (problem.isPrivate(i)) module.nextColumn("(private)");
      module.println();
    }
    // if nothing was printed, at least print the name (as we might refer to it later)
    if (counter == 0) { module.nextColumn(name); module.println("[empty set of DPs]"); }
    module.endTable();
  }
  
  /** This prints the list of rules of the given problem to the output module, including a name. */
  private void printRules(OutputModule module, Problem problem, String name) {
    module.startTable();
    int counter = 0;
    for (Rule rule : problem.getRuleList()) {
      module.nextColumn(counter == 0 ? name + "." : "");
      counter++;
      module.nextColumn("(%a)", counter);
      module.nextColumn("%a", rule);
      module.println();
    }
    // if nothing was printed, at least print the name (as we might refer to it later)
    if (counter == 0) { module.nextColumn(name); module.println("[empty set of rules]"); }
    module.endTable();
  }

  /**
   * Helper function for justify: sets up the maps that track the problems, DP lists and rule lists
   * that we have encountered so far, and prints the information for the initial DP problem.
   */
  private void justifyStart(OutputModule module, HashMap<Problem,String> probnames,
                            HashMap<List<DP>,String> pnames,
                            HashMap<FixedList<Rule>,String> rnames) {
    storeDPP(_initialProblem, probnames);
    boolean dpnew = storeDPList(_initialProblem, pnames);
    boolean rnew = storeRuleList(_initialProblem, rnames);
    module.print("We start by computing the initial DP problem ");
    printDPP(module, _initialProblem, probnames, pnames, rnames);
    module.println(", where:");
    if (dpnew) printDPs(module, _initialProblem, pnames.get(_initialProblem.getDPList()));
    if (rnew) printRules(module, _initialProblem, rnames.get(_initialProblem.getRuleList()));
  }

  /**
   * Helper function for justify: this goes over each of the processors in turn and prints the
   * input, processor justification, and result of the processor.  In doing so, we give names to
   * all the DP problems we encounter, as well as their sets of DPs and rules.
   */
  private void justifyProcessor(OutputModule module, ProcessorProofObject po,
                                HashMap<Problem,String> probnames, HashMap<List<DP>,String> pnames,
                                HashMap<FixedList<Rule>, String> rnames) {
    module.print("***** We apply the %a Processor on ", po.queryProcessorName());
    Problem input = po.queryInput();
    if (!probnames.containsKey(input)) {
      describeUnknownDPP(module, input, probnames, pnames, rnames);
    }
    else {
      printDPP(module, input, probnames, pnames, rnames);
      module.println(".");
    }
      
    po.justify(module);

    ArrayList<Problem> newDPs = new ArrayList<Problem>();
    ArrayList<Problem> newRules = new ArrayList<Problem>();
    for (Problem out : po.queryResults()) {
      storeDPP(out, probnames);
      if (storeDPList(out, pnames)) newDPs.add(out);
      if (storeRuleList(out, rnames)) newRules.add(out);
    }

    module.print("Processor output: { ");
    boolean first = true;
    for (Problem out : po.queryResults()) {
      if (first) first = false;
      else module.print("; ");
      printDPP(module, out, probnames, pnames, rnames);
      module.print(" ");
    }
    if (newDPs.size() == 0 && newRules.size() == 0) module.println("}.");
    else {
      module.println("}, where:");
      for (Problem prob : newDPs) printDPs(module, prob, pnames.get(prob.getDPList()));
      for (Problem prob : newRules) printRules(module, prob, rnames.get(prob.getRuleList()));
    }
  }
  
  private void justifyEnd(OutputModule module, HashMap<Problem,String> probnames,
                          HashMap<List<DP>,String> pnames, HashMap<FixedList<Rule>,String> rnames) {
    if (_failure != null) {
      module.print("***** No progress could be made on DP problem ");
      if (probnames.containsKey(_failure)) {
        printDPP(module, _failure, probnames, pnames, rnames);
        module.println(".");
      }
      else describeUnknownDPP(module, _failure, probnames, pnames, rnames);
    }
  }

  /**
   * Although in principle we should only be given proof objects whose input is a DP problem that
   * was generated as the output of a previous processor, it is possible that something goes wrong
   * in the proof and a subproof is omitted.  For this special case, we just write out what the
   * problem and its rules are; we do not name them, and do not check if they already have a name.
   */
  private void describeUnknownDPP(OutputModule module, Problem problem, HashMap<Problem,String>
                                  probnames, HashMap<List<DP>,String> pnames,
                                  HashMap<FixedList<Rule>, String> rnames) {
    storeDPP(problem, probnames);
    boolean dpnew = storeDPList(problem, pnames);
    boolean rnew = storeRuleList(problem, rnames);
    module.print("the DP problem ");
    printDPP(module, problem, probnames, pnames, rnames);
    if (dpnew || rnew) module.println(", where:");
    else module.println();
    if (dpnew) printDPs(module, problem, pnames.get(problem.getDPList()));
    if (rnew) printRules(module, problem, rnames.get(problem.getRuleList()));
  }

  /**
   * This function handles the printing of a DP with a previously-fixed renaming for all its
   * components, by translating it into a single Pair that the OutputModule knows how to print.
   */
  private Pair<String,Object[]> makeDPObject(DP dp, Renaming naming) {
    StringBuilder ret = new StringBuilder("%a %{thickArrow} %a");
    ArrayList<Object> args = new ArrayList<Object>(4);
    args.add(new Pair<Term,Renaming>(dp.lhs(), naming));
    args.add(new Pair<Term,Renaming>(dp.rhs(), naming));

    if (!dp.constraint().isValue() || !dp.constraint().toValue().getBool()) {
      ret.append(" | %a");
      args.add(new Pair<Term,Renaming>(dp.constraint(), naming));
    }

    boolean anynew = false;
    for (Variable x : dp.lvars()) {
      if (!dp.constraint().freeReplaceables().contains(x)) anynew = true;
    }
    if (anynew) {
      ret.append(" { ");
      boolean first = true;
      for (Variable x : dp.lvars()) {
        if (naming.getName(x) == null) continue;  // if it doesn't occur in the terms
                                                  // it's only confusing if we list it here
        if (!first) ret.append(", ");
        first = false;
        ret.append("%a");
        args.add(new Pair<Term,Renaming>(x, naming));
      }
      ret.append(" }");
    }

    return new Pair<String,Object[]>(ret.toString(), args.toArray());
  }

  /**
   * This function handles the printing of a DP, by translating it into a Pair that the OutputModule
   * knows how to print (but with good use of variables, and cleverly printing only those
   * constraints and variables that we have to).
   */
  private Pair<String,Object[]> makeDPObject(DP dp, OutputModule module) {
    Renaming naming =
      module.queryTermPrinter().generateUniqueNaming(dp.lhs(), dp.rhs(), dp.constraint());
    return makeDPObject(dp, naming);
  }

  /** We use this adapted OutputModule for printing, so we can naturally handle dependency pairs. */
  private class OutputModuleWithDependencyPairs extends OutputModuleAdapter {
    public OutputModuleWithDependencyPairs(OutputModule m) { super(m); }
    protected Object alterObject(Object ob) {
      if (ob instanceof DP dp) return makeDPObject(dp, _module);
      if (ob instanceof Pair p) {
        if (p.fst() instanceof DP dp && p.snd() instanceof Renaming r) {
          return makeDPObject(dp, r);
        }
      }
      return null;
    }
  }
}

