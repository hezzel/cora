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

package charlie.smt;

import static org.junit.jupiter.api.Assertions.assertTrue;
import java.util.ArrayList;

/**
 * A fake Smt solver for the purpose of testing: it stores the questions it receives, and gives the
 * answers it's been instructed to give.  This is only meant for validity checks; if any
 * satisfiability checks are done, then false is asserted instead.
 */
public class FixedAnswerValidityChecker implements SmtSolver {
  private boolean[] _answers;
  private int _defaultAnswer;
  private ArrayList<String> _questions;

  /**
   * Sets up the solver to give the given answers, in order.  Once these have all been given, false
   * will be asserted, unless setDefaultAnswer has been called, in which case the default answer
   * will be returned afterwards.
   */
  public FixedAnswerValidityChecker(boolean ...answers) {
    _answers = answers;
    _defaultAnswer = 0;
    _questions = new ArrayList<String>();
  }

  public void setDefaultAnswer(boolean answer) {
    if (answer) _defaultAnswer = 1;
    else _defaultAnswer = -1;
  }

  public Answer checkSatisfiability(SmtProblem problem) {
    assertTrue(false, "The FixedAnswerValidityChecker was asked for satisfiability!");
    return new Answer.MAYBE("FixedAnswerValidityChecker");
  }

  public boolean checkValidity(SmtProblem problem) {
    int k = _questions.size();
    _questions.add(problem.toString());
    if (k < _answers.length) return _answers[k];
    if (_defaultAnswer != 0) return _defaultAnswer > 0;
    assertTrue(false, "The FixedAnswerValidityChecker was asked for an answer " + (k+1) +
      " times while only " + _answers.length + " answers were given and no default was set.");
    return false;
  }

  public int queryNumberQuestions() {
    return _questions.size();
  }

  public String queryQuestion(int index) {
    return _questions.get(index);
  }
}
