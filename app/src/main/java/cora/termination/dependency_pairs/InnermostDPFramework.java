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

import charlie.trs.TRS;
import cora.termination.reduction_pairs.horpo.Horpo;
import cora.termination.dependency_pairs.processors.*;
import cora.termination.dependency_pairs.processors.graph.GraphProcessor;
import cora.termination.dependency_pairs.processors.graph.ReachabilityProcessor;

public class InnermostDPFramework extends DPFramework {
  private boolean _extraRules;
  private Processor[] _processors;
  private int RESTARTLOOP;
    // this is the number of processors we do before starting the main loop,
    // mostly to take advantage of the public/private information
  private int THEORINDEX;

  /**
   * Create a DP framework for innermost termination and the given rules.  If extraRules is set to
   * true, then an arbitrary number of additional, unknown defined symbols and rules defining them
   * may be present in the TRS (as well as additional sorts and constructors defining those, but not
   * additional constructors of the existing sorts, nor rules defining any known symbol).
   */
  public InnermostDPFramework(TRS trs, boolean extraRules) {
    super(trs, true, extraRules);
    _processors = new Processor[] {
        new SplittingProcessor(),
        new TheoryArgumentsProcessor(true),
        new ReachabilityProcessor(),
        new GraphProcessor(),
        new ChainingProcessor(false),
        new SubtermProcessor(),
        new IntegerMappingProcessor(),
        new TheoryArgumentsProcessor(false),
        new UsableRulesProcessor(),
        new ReductionPairProcessor(new Horpo(false))
      };
    RESTARTLOOP = 3;
  }

  protected Processor getProcessor(int index) {
    return _processors[index];
  }

  protected int getInitialProcessorIndex(Problem initialProblem) {
    return 0;
  }

  /**
   * If the last was a success, we restart the main loop AFTER the initial processors.
   * If not, we just try the next processor in the sequence.
   */
  protected int getNextProcessorIndex(int lastIndex, int lastSuccess, Problem problem) {
    if (lastSuccess == SUCCESS) {
      int RESTARTLOOP = 3;
      if (lastIndex < RESTARTLOOP) return lastIndex + 1;
      else return RESTARTLOOP;
    }
    else if (lastIndex < _processors.length - 1) return lastIndex + 1;
    return -1;
  }
}

