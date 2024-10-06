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

package cora.termination.dependency_pairs.processors;

import java.util.List;

import cora.io.DefaultOutputModule;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.Problem;

/**
 * A ProcessorProofObject holds the results of a processor: the input DP problem, the resulting
 * set, and any necessary information to justify the proof.
 */
public abstract class ProcessorProofObject {
  protected Problem _input;
  protected List<Problem> _output;

  /** Initialises a successful proof with the given input and output. */
  protected ProcessorProofObject(Problem input, List<Problem> output) {
    _input = input;
    _output = output;
  }

  /** Initialises a successful proof with the given input and singleton list of output. */
  protected ProcessorProofObject(Problem input, Problem output) {
    _input = input;
    if (output.isEmpty()) _output = List.of();
    else _output = List.of(output);
  }

  /** Initialises an unsuccessful proof with the given input. */
  protected ProcessorProofObject(Problem input) {
    _input = input;
    _output = null;
  }

  /** Returns true if the processor was successful, and the output is changed from the input. */
  public boolean applicable() {
    return _output != null && (_output.size() != 1 || _output.get(0) != _input);
  }

  /** Returns the input problem to this processor. */
  public Problem queryInput() { return _input; }

  /**
   * If the result is a singleton, this returns just the result.
   * If not, an Error is thrown, because this really shouldn't be called if there is any chance of
   * the processor returning a list with more than one element.
   * (If the output is the empty list, then the empty DP Problem is returned.  If the problem is
   * not applicable, then the input is returned.)
   */
  public Problem queryOutput() {
    if (_output == null) return _input;
    if (_output.size() == 0) {
      return new Problem(List.of(), _input.getRuleList(), null, _input.getOriginalTRS(),
        _input.isInnermost(), _input.hasExtraRules(), _input.queryTerminationStatus());
    }
    if (_output.size() == 1) return _output.get(0);
    throw new Error("Calling queryOutput() when there are " + _output.size() + " results!");
  }

  /** Returns the output problems to this processor. */
  public List<Problem> queryResults() { return _output; }

  /** This prints the reasoning for the processor to the given output module. */
  public abstract void justify(OutputModule module);

  /** This returns the name of the processor (e.g., Reachability, Subterm Criteiron). */
  public abstract String queryProcessorName();

  @Override
  public String toString() {
    OutputModule module = DefaultOutputModule.createPlainModule();
    justify(module);
    String justification = module.toString();
    return queryProcessorName() + "\n" + justification;
  }
}

