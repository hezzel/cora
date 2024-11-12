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

import charlie.util.Pair;
import charlie.trs.TRS;
import charlie.trs.TrsProperties.*;
import cora.io.OutputModule;
import cora.io.ProofObject;
import cora.config.Settings;
import cora.termination.dependency_pairs.processors.Processor;
import cora.termination.dependency_pairs.processors.ProcessorProofObject;

import java.util.LinkedList;
import java.util.Set;

public abstract class DPFramework {
  private ProofObject _applicability;
  private Problem _initialProblem;
  protected final int SUCCESS = 1;
  protected final int FAILURE = -1;
  protected final int NA = 0;

  /** The code users have to use with --disable to disable any use of the DP framework. */
  public static String queryDisabledCode() {
    return "dp";
  }

  /** The code users have to use with --disable to disable use of the public/privte information. */
  public static String queryPrivateDisabledCode() {
    return "private";
  }

  /** Children should call this with the TRS that we are going to try to apply the method on. */
  protected DPFramework(TRS trs, boolean innermost, boolean extraRules) {
    _applicability = determineApplicability(trs);
    DPGenerator generator = new DPGenerator(trs);
    _initialProblem = generator.queryProblem(innermost, extraRules);
    if (Settings.isDisabled(queryPrivateDisabledCode())) {
      _initialProblem = _initialProblem.removeDPs(Set.of(), true);
    }
  }

  /**
   * Helper function for the constructor: this determines if the method is applicable at all.  This
   * is both a test on whether the TRS has the right form (e.g., left-hand sides are patterns, no
   * lambdas allowed for now), and if the accessibility requirements are satisfied.
   *
   * Protected because inheriting classes can override it; they are not expected to call it,
   * however, since this is only meant as a helper function for the constructor.
   */
  protected ProofObject determineApplicability(TRS trs) {
    if (!trs.verifyProperties(Level.APPLICATIVE, Constrained.YES, TypeLevel.SIMPLE,
                              Lhs.PATTERN, Root.THEORY)) {
      return new ProofObject() {
        public Answer queryAnswer() { return Answer.NO; }
        public void justify(OutputModule o) {
          o.println("For now, static dependency pairs can only be applied on applicative " +
            "systems without tuples, where the left-hand sides of rules are patterns of the form " +
            "f(l1,...,lk) with f a function symbol.");
          o.println("(Note: extensions matter! If you are using an input file that describes for " +
            "instance a first-order or applicative TRS, but use the extension of a format that " +
            "allows for the inclusion of abstractions or product types, then these constructions " +
            "are implicitly allowed to occur in terms, and hence the framework is not applicable.");
        }
      };
    }
    if (Settings.isDisabled(queryDisabledCode())) {
      return new ProofObject() {
        public Answer queryAnswer() { return Answer.NO; }
        public void justify(OutputModule o) {
          o.println("Use of the dependency pair framework is disabled through runtime settings.");
        }
      };
    }
    AccessibilityChecker checker = new AccessibilityChecker(trs);
    return checker.checkAccessibility();
  }

  /**
   * All inheriting classes should implement this: this maps a processor INDEX to an actual
   * processor.  This will only ever be called with a non-negative index as returned by either
   * getInitialProcessorIndx or getNextProcessorIndex; this may not return null.
   */
  protected abstract Processor getProcessor(int index);

  /**
   * Inheriting classes should implement this: this should return the index of the first processor
   * to try on the given initial problem.  It should always return a non-negative integer (for
   * which getProcessor returns a value).
   */
  protected abstract int getInitialProcessorIndex(Problem initialProblem);

  /**
   * Inheriting classes should implement this: this should return the index of the next processor
   * to try on the given problem, or a negative number if there is nothing more to try; the process
   * has failed.
   * 
   * Here, lastSuccess is one of SUCCESS, FAILURE or NA.
   * 
   * - In the case of SUCCESS, this is a problem we haven't tried to use any processors on before.
   *   Rather, its parent problem was simplified using the processor with lastIndex.
   * - In the case of FAILURE or NA, a previous processor (with index lastIndex) was tried on this
   *   problem, but either failed, or replied that it was not applicable.
   */
  protected abstract int getNextProcessorIndex(int lastIndex, int lastSuccess, Problem problem);

  /**
   * External objects may call this to query the applicability of the method before trying to run
   * the method.  Doing so is not necessary; it is checked regardless when trying to generate a
   * proof by dependency pairs.  However, it may be useful to determine what to do next.
   */
  public final ProofObject checkApplicable() {
    return _applicability;
  }

  /**
   * The main functionality of the framework.  After creating the framework, call this to try to
   * determine termination using the relevant instance of the DP framework.
   */
  public final DPProofObject run() {
    if (_applicability.queryAnswer() != ProofObject.Answer.YES) {
      return new DPProofObject(_applicability);
    }

    LinkedList< Pair<Problem,Integer> > todo = new LinkedList< Pair<Problem,Integer> >();
    DPProofObject ret = new DPProofObject(_applicability, _initialProblem);
    Problem problem = _initialProblem;
    int processorIndex = getInitialProcessorIndex(problem);

    /**
     * We iterate as follows: we have one problem, and a todo list of other problems to look at.
     * In each step, we choose a processor based on the problem, the last processor that was applied
     * on that problem (or the parent problem), and whether or not this last processor was
     * successful.  If we eventually discover that there's no processor anymore that we can try, the
     * process fails (in this case, processorIndex returns a negative number).  Alternatively, if
     * the processor returns no new problems, and the todo list is also empty, we conclude success.
     */
    while (processorIndex >= 0) {
      Processor proc = getProcessor(processorIndex);
      int status;
      if (proc.isApplicable(problem)) {
        ProcessorProofObject ppo = proc.processDPP(problem);
        if (ppo.applicable()) {
          for (Problem p : ppo.queryResults()) {
            todo.add(new Pair<Problem,Integer>(p, processorIndex));
          }
          ret.addProcessorProof(ppo);
          if (todo.isEmpty()) {
            ret.setTerminating();
            return ret;
          }
          Pair<Problem,Integer> pair = todo.removeFirst();
          problem = pair.fst();
          processorIndex = pair.snd();
          status = SUCCESS;
        }
        else status = FAILURE;
      }
      else status = NA;

      processorIndex = getNextProcessorIndex(processorIndex, status, problem);
    }
    ret.setFailedProof(problem);
    return ret;
  }
}

