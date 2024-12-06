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

package charlie.smt;

/**
 * An SmtSolver is an object that takes a Constraint and determines its satisfiability or validity.
 */
public interface SmtSolver {
  sealed interface Answer permits Answer.YES, Answer.NO, Answer.MAYBE {
    boolean isYes();
    public record YES(Valuation val) implements Answer { public boolean isYes() { return true; } }
    public record NO() implements Answer { public boolean isYes() { return false; } }
    public record MAYBE(String reason) implements Answer { public boolean isYes() { return false; } }
  }

  /**
   * Given an SmtProblem, this function tries to find a valuation for the variables in the problem
   * that satisfies all the constraints stored in the problem.
   * If successful, returns YES(valuation).
   * If we determine such a valuation cannot exist, returns NO(valuation).
   * If the search for a valuation fails but we cannot prove non-existence, returns MAYBE(reason).
   * The reason could for instance be something like "External SMT solver file is missing",
   * "SMT solver failed to find a solution", or "Internal SMT solver cannot handle non-linear
   * arithmetic".
   */
  Answer checkSatisfiability(SmtProblem problem);

  /**
   * Given an SmtProblem, this function tries to prove that it is valid.  This either succeeds, in
   * which case true is returned, or fails, in which case false is returned.
   *
   * Note that failure could either be because the problem is NOT valid, or because the SMT solver
   * simply could not determine whether a solution exists.
   */
  boolean checkValidity(SmtProblem problem);
}
