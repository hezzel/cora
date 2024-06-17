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

import java.util.ArrayList;
import java.util.HashMap;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Variable;
import charlie.terms.Renaming;
import cora.io.OutputModule;
import cora.io.OutputModuleAdapter;
import cora.io.ProofObject;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

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
   * This marks the proof as abandoned, with the given DP Problem being unsimplifable.
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

    HashMap<Problem,String> names = new HashMap<Problem,String>();
    names.put(_initialProblem, "P1");
    module.println("We start by computing the following initial DP problem:");
    printDPP(module, _initialProblem, "P1");
    int count = 1;
    for (ProcessorProofObject po : _processorProofs) {
      module.print("***** We apply the %a Processor on ", po.queryProcessorName());
      if (!names.containsKey(po.queryInput())) {
        module.println("The following DP problem:");
        printDPP(module, po.queryInput(), "");
      }
      else module.println(names.get(po.queryInput()) + ".");
      po.justify(module);
      for (Problem out : po.queryResults()) {
        count++;
        String name = "P" + count;
        names.put(out, name);
        printDPP(module, out, name);
      }
    }
    if (_failure != null) {
      module.print("***** No progress could be made on DP problem");
      if (names.containsKey(_failure)) module.println(" %a.", names.get(_failure));
      else { module.println(":"); printDPP(module, _failure, ""); }
    }
  }

  /** This prints a DP Problem to the output module, including a name. */
  private void printDPP(OutputModule module, Problem prob, String name) {
    module.startTable();
    int counter = 0;
    for (DP dp : prob.getDPList()) {
      module.nextColumn(counter == 0 ? name + "." : "");
      counter++;
      module.nextColumn("(%a)", counter);
      module.nextColumn("%a", makeDPObject(dp, module));
      module.println();
    }
    // if nothing was printed, at least print the name (as we might refer to it later)
    if (counter == 0) { module.nextColumn(name); module.println("[empty DP problem]"); }
    module.endTable();
  }

  /**
   * This function handles the printing of a DP, by translating it into a Pair that the OutputModule
   * knows how to print (but with good use of variables, and cleverly printing only those
   * constraints and variables that we have to).
   */
  private Pair<String,Object[]> makeDPObject(DP dp, OutputModule module) {
    Renaming naming =
      module.queryTermPrinter().generateUniqueNaming(dp.lhs(), dp.rhs(), dp.constraint());

    StringBuilder ret = new StringBuilder("%a %{thickArrow} %a");
    ArrayList<Object> args = new ArrayList<Object>();
    args.add(new Pair<Term,Renaming>(dp.lhs(), naming));
    args.add(new Pair<Term,Renaming>(dp.rhs(), naming));

    if (!dp.constraint().isValue() || !dp.constraint().toValue().getBool()) {
      ret.append(" | %a");
      args.add(new Pair<Term,Renaming>(dp.constraint(), naming));
    }

    boolean anynew = false;
    for (Variable x : dp.vars()) {
      if (!dp.constraint().freeReplaceables().contains(x)) anynew = true;
    }
    if (anynew) {
      ret.append(" { ");
      boolean first = true;
      for (Variable x : dp.vars()) {
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

  /** We use this adapted OutputModule for printing, so we can naturally handle dependency pairs. */
  private class OutputModuleWithDependencyPairs extends OutputModuleAdapter {
    public OutputModuleWithDependencyPairs(OutputModule m) { super(m); }
    protected Object alterObject(Object ob) {
      if (ob instanceof DP dp) return makeDPObject(dp, _module);
      return null;
    }
  }
}

