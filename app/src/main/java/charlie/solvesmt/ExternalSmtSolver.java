/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.solvesmt;

import java.io.*;
import java.util.List;
import java.util.Scanner;
import charlie.exceptions.ParseError;
import charlie.smt.*;
import org.jetbrains.annotations.NotNull;

/**
 * An ExternalSmtSolver is a solver that operates by writing a file and calling a fixed external SMT solver.
 * The output file of the solver is read to find the valuation.
 * Note: the idea of calling an external program directly through the "Runtime" caller is outdated
 * and is planned to be phased out in the future.
 */
public class ExternalSmtSolver implements SmtSolver {
 /**
   * This creates a file for the SMT solver.
  * If creating the file fails for some reason, an IOException is thrown instead.
   */
  private void createSmtFile(int numbool, int numint, Constraint constraint) throws IOException {

    BufferedWriter writer =
      new BufferedWriter(new FileWriter("problem.smt2"));

    SMTLibString file =
      new SMTLibString(SMTLibString.Version.V26, SMTLibString.Logic.QFNIA);

    String stringOfFile =
      file.buildSmtlibString(numbool, numint, constraint);

    writer.write(stringOfFile);

    writer.close();
  }

  /**
   * This function runs the SMT solver on problem.smt2.  If this fails for whatever reason, an
   * Exception is thrown instead.
   */
  private void runSmtSolver() throws IOException, InterruptedException {
    Runtime rt = Runtime.getRuntime();
    // clean up old result, it any
    try { Process p = rt.exec(new String[] {"rm", "result"}); p.waitFor(); } catch (Exception e) {}
    // start new satsolver process
    Process p = rt.exec(new String[] {"./smtsolver", "problem.smt2", "result" });
    p.waitFor();
  }

  /**
   * This reads the answer the SMT solver printed to the result file.  It will be either sat,
   * unsat, or a different string which should be expected to correspond to "maybe".  If the file
   * cannot be read ,then null is returned or an IOException thrown, as appropriate.
   */
  private String readAnswer() throws IOException {
    File file = new File("result");
    Scanner reader = new Scanner(file);

    return SMTLibResponseHandler.readAnswer(reader);
  }

  /**
   * This reads the solution from the expected SMT output file, and returns the corresponding
   * Answer.
   * If the file cannot be read -- for example because the SMT solver failed -- then MAYBE is
   * returned (with an appropriate failure meesage).  The same holds if satisfiability could not
   * be determined.  If the result is not satisfiable, then NO is returned.
   */
  private Answer readSmtFile() throws IOException {
    List<SExpression> exprs = SmtParser.readExpressionsFromFile("result");

    return SMTLibResponseHandler.expressionsToAnswer(exprs);

  }

  /**
   * Primary access function.  This generates an SMT file from the given SMT problem, executes the
   * SMT solver on it, and reads the result file to obtain a suitable Valuation -- or concludes
   * that no proof can be found.
   */
  public Answer checkSatisfiability(@NotNull SmtProblem problem) {
    Constraint combinedConstraints = problem.queryCombinedConstraint();
    try {
      createSmtFile(problem.numberBooleanVariables(), problem.numberIntegerVariables(), combinedConstraints);
    }
    catch (IOException e) {
      return new Answer.MAYBE("Could not create SMT file: " + e.getMessage());
    }

    try { runSmtSolver(); }
    catch (IOException e) {
      return new Answer.MAYBE("Could not execute SMT solver: " + e.getMessage());
    }
    catch (InterruptedException e) {
      return new Answer.
        MAYBE(STR."""
          Waiting for external SMT solver was interrupted: \{e.getMessage()}
          (Warning: the SMT solver may still be running in the background.  If so, you may need to kill it."""
      );
    }

    Answer ret;
    try { ret = readSmtFile(); }
    catch (IOException e) {
      return new Answer.MAYBE(STR."Error reading result file: \{e.getMessage()}");
    }
    catch (ParseError e) {
      return new Answer.MAYBE(STR."Parsing error reading result file: \{e.getMessage()}");
    }

    switch (ret) {
      case Answer.YES(Valuation val):
        if (!combinedConstraints.evaluate(val)) return new Answer.MAYBE("Valuation read from external solver " +
          "does not satisfy the constraint!");
      default:
        return ret;
    }
  }

  /**
   * This checks the satisfiability of the negation of the constraint obtained from the given
   * SmtProblem, since unsatisfiability implies that the original constraint is valid.  No
   * valuation is read; we trust the answer of the SMT solver.
   */
  public boolean checkValidity(SmtProblem problem) {
    Constraint negated = SmtFactory.createNegation(problem.queryCombinedConstraint());
    try {
      createSmtFile(problem.numberBooleanVariables(), problem.numberIntegerVariables(), negated);
      runSmtSolver();
      return readAnswer().equals("unsat");
    }
    catch (Exception e) { return false; } // we could not conclude validity
  }
}
