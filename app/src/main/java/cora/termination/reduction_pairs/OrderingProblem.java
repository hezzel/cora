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

package cora.termination.reduction_pairs;

import java.util.ArrayList;
import java.util.List;
import java.util.Collections;

import charlie.util.Pair;
import charlie.trs.TRS;
import charlie.smt.Constraint;
import cora.io.OutputModule;
import cora.io.DefaultOutputModule;
import cora.termination.reduction_pairs.OrderingRequirement.Relation;

/**
 * An OrderingProblem represents a list of requirements s ≻ t / s ≽ t that should be satisfied by
 * a reduction pair.  In addition, some requirements may only be required conditionally on some
 * constraint, and for some requirements we may want to prove *either* s ≻ t *or* s ≽ t, with at
 * least one of those special requirements oriented strictly (so using ≻).
 *
 * The OrderingProblem keeps track of a TRS to impose the restrictions of term formation; its rules
 * are not directly used.
 */
public class OrderingProblem {
  private List<OrderingRequirement> _alwaysReqs;
  private List<Pair<Constraint,OrderingRequirement>> _conditionalReqs;
  private List<Pair<Integer,OrderingRequirement>> _eitherReqs;
  private TRS _originalTRS;
  private Monotonicity _monotonicity;

  /**
   * Creates an empty OrderingProblem, with restrictions on term formation based on the given TRS,
   * and using the given monotonicity requirements.
   */
  public OrderingProblem(TRS original, Monotonicity mono) {
    _alwaysReqs = new ArrayList<OrderingRequirement>();
    _conditionalReqs = new ArrayList<Pair<Constraint,OrderingRequirement>>();
    _eitherReqs = new ArrayList<Pair<Integer,OrderingRequirement>>();
    _originalTRS = original;
    _monotonicity = mono;
  }

  /** Returns the origin TRS, which is relevant for the restrictions on term formation. */
  public TRS queryOriginalTRS() {
    return _originalTRS;
  }

  /** Returns the monotonicity requirements a reduction pair for this problem must satisfy. */
  public Monotonicity queryMonotonicity() {
    return _monotonicity;
  }

  /**
   * Adds the given ordering requirement to the problem unconditionally: this must hold
   * regardless of anything else in the SMT problem, and if it doesn't, the reduction pair fails.
   */
  public void require(OrderingRequirement req) {
    _alwaysReqs.add(req);
  }

  /**
   * Conditionally adds the given ordering requirement to the problem; that is, it should be
   * satisfied if the constraint evaluates to true, and otherwise can be ignored.
   */
  public void requireConditionally(OrderingRequirement req, Constraint constraint) {
    _conditionalReqs.add(new Pair<Constraint,OrderingRequirement>(constraint, req));
  }

  /**
   * Adds the given OrderingRequirement -- for which it does not matter if it is a Greater or Geq
   * requirement -- as an "either" requirement: if any either requirements are given, then at least
   * one must be oriented strictly, and the rest must be oriented strictly or weakly.
   * Each Either requirement should come with a unique identifier, which can be used to query the
   * strict/weak orientation status after an OrderingProblem has been oriented.
   */
  public void requireEither(OrderingRequirement req, int identifier) {
    _eitherReqs.add(new Pair<Integer,OrderingRequirement>(identifier, req));
  }

  /** Returns the list of either reqs, each with their unique identifier */
  public List<Pair<Integer,OrderingRequirement>> eitherReqs() {
    return Collections.unmodifiableList(_eitherReqs);
  }

  /** Returns the list of conditional requirements, each along with its condition */
  public List<Pair<Constraint,OrderingRequirement>> conditionalReqs() {
    return Collections.unmodifiableList(_conditionalReqs);
  }

  /** Returns the list of requirements we always have to satisfy */
  public List<OrderingRequirement> unconditionalReqs() {
    return Collections.unmodifiableList(_alwaysReqs);
  }
  
  /**
   * Returns a string representative of the problem.
   * This is only meant for debug output!
   */
  public String toString() {
    StringBuilder builder = new StringBuilder();
    for (OrderingRequirement req : _alwaysReqs) builder.append("U) " + req.toString() + "\n");
    for (Pair<Constraint,OrderingRequirement> p : _conditionalReqs) {
      builder.append("C) " + p.fst() + "  ==>  " + p.snd() + "\n");
    }
    for (Pair<Integer,OrderingRequirement> p : _eitherReqs) {
      builder.append("E) " + p.fst() + "  :  " + p.snd() + "\n");
    }
    return builder.toString();
  }
}

