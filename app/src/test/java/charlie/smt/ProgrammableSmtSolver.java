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
import java.util.TreeMap;

/**
 * A fake Smt solver for the purpose of testing: it is programmed with expected questions and their
 * answers, and stores how many times each question is asked.  If a question is asked that is not
 * pre-programmed, false is asserted.
 */
public class ProgrammableSmtSolver implements SmtSolver {
  private TreeMap<String,Answer> _answers;
  private TreeMap<String,Integer> _count;

  /** Sets up the solver without answers. */
  public ProgrammableSmtSolver() {
    _answers = new TreeMap<String,Answer>();
    _count = new TreeMap<String,Integer>();
  }

  /** Sets up the solver with one question/answer combination. */
  public ProgrammableSmtSolver(String question, Answer answer) {
    _answers = new TreeMap<String,Answer>();
    _count = new TreeMap<String,Integer>();
    storeAnswer(question, answer);
  }

  /** Sets up the solver with two question/answer combinations. */
  public ProgrammableSmtSolver(String q1, Answer a1, String q2, Answer a2) {
    _answers = new TreeMap<String,Answer>();
    _count = new TreeMap<String,Integer>();
    storeAnswer(q1, a1);
    storeAnswer(q2, a2);
  }

  /** Sets up the solver with three question/answer combinations. */
  public ProgrammableSmtSolver(String q1, Answer a1, String q2, Answer a2,
                               String q3, Answer a3) {
    _answers = new TreeMap<String,Answer>();
    _count = new TreeMap<String,Integer>();
    storeAnswer(q1, a1);
    storeAnswer(q2, a2);
    storeAnswer(q3, a3);
  }

  /** Store an answer for the SMT-solver to give to the given question. */
  public void storeAnswer(String question, Answer answer) {
    _answers.put(question, answer);
    _count.put(question, 0);
  }

  public Answer checkSatisfiability(SmtProblem problem) {
    String prob = problem.toString().strip();
    if (!_answers.containsKey(prob)) {
      assertTrue(false, "Unexpected question " + prob + " to ProgrammableSmtSolver!");
    }
    return _answers.get(prob);
  }

  public boolean checkValidity(SmtProblem problem) {
    String question = problem.queryCombinedConstraint().negate().toString().strip();
    if (!_answers.containsKey(question)) {
      assertTrue(false, "Validity check causes unexpected question " + question +
        " in ProgrammableSmtSolver!");
    }
    return _answers.get(question) instanceof Answer.NO;
  }

  public int queryQuestionCount(String question) {
    return _count.get(question);
  }
}
