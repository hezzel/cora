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

package charlie.solvesmt;

import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.io.File;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Scanner;
import charlie.exceptions.NullStorageException;
import charlie.util.ExceptionLogger;
import charlie.smt.*;
import charlie.util.ProcessCaller;
import static charlie.solvesmt.SMTLibString.Version.V26;
import static charlie.solvesmt.ProcessSmtSolver.PhysicalSolver.Z3;

public class ProcessSmtSolver implements SmtSolver {
  public static int TIMEOUT = 10;

  public enum PhysicalSolver {
    // Possible solvers supported by the process caller.
    // Note: for security reasons, we do not allow the user to input any command to be executed as
    // solver.  So this list keeps all the possible ones here and only those can be called via the
    // process caller.

    Z3, YICES2, CVC5;

    @Override
    public String toString() {
      return switch (this) {
        case Z3 -> "Z3";
        case YICES2 -> "YICES 2";
        case CVC5 -> "CvC 5";
      };
    }

    @Contract(pure = true)
    public @NotNull String getCommandName() {
      return switch (this) {
        case Z3: yield  "z3";
        case CVC5: yield  "cvc";
        case YICES2: yield  "yices-smt2";
      };
    }
  }

  /** Returns the PhysicalSolver matching the given name, if any; null otherwise. */
  public static PhysicalSolver stringToSolver(String name) {
    name = name.toLowerCase();
    if (name.equals("z3")) return PhysicalSolver.Z3;
    if (name.equals("cvc5") || name.equals("cvc")) return PhysicalSolver.CVC5;
    if (name.equals("yices2") || name.equals("yices")) return PhysicalSolver.YICES2;
    return null;
  }

  private final PhysicalSolver _physicalSolver;

  /** Sets up an SmtSolver that uses the default solver (this is currently set to Z3). */
  public ProcessSmtSolver() {
    _physicalSolver = Z3;
  }

  public ProcessSmtSolver(@NotNull PhysicalSolver physicalSolver) {
    if (physicalSolver == null) throw new NullStorageException(
      "ProcessSmtSolver",
      "Cannot initialise a null Physical Solver"
    );

    _physicalSolver = physicalSolver;
  }

  /** Create a process caller for the given input file with SMT problem, with the given timeout (in
   * seconds). */
  private ProcessCaller createSmtSolverProcess(Path smtProblemFile, int timeout) {
    List<String> commands = new ArrayList<>();

    commands.add(_physicalSolver.getCommandName() + " " + smtProblemFile.toString());

    return new ProcessCaller(commands, timeout);
  }

  /**
   * Given an SmtProblem, this function tries to find a valuation for the variables in the problem
   * that satisfies all the constraints stored in the problem.
   * If successful, returns YES(valuation).
   * If we determine such a valuation cannot exist, returns NO().
   * If the search for a valuation fails but we cannot prove non-existence, returns MAYBE(reason).
   * The reason could for instance be something like "External SMT solver file is missing",
   * "SMT solver failed to find a solution", or "Internal SMT solver cannot handle non-linear
   * arithmetic".
   *
   * @param problem
   */
  @Override
  public Answer checkSatisfiability(SmtProblem problem) {
    SMTLibString file = new SMTLibString(V26);
    String stringOfSmtProblem = file.buildSmtlibString(problem);
    String smtResultString;
    try {
      Path smtProblemFile = Files.createTempFile("coraSMTTask_sat_", null);
      Files.writeString(smtProblemFile, stringOfSmtProblem);

      ProcessCaller pc = createSmtSolverProcess(smtProblemFile, TIMEOUT);
      Optional<String> optionalSmtResultString = pc.getResultAsString();

      Files.delete(smtProblemFile);

      if (!optionalSmtResultString.isPresent()) {
        return new Answer.MAYBE("SMT solver process did not return an answer within the " +
                                "time limit.");
      }
      smtResultString = optionalSmtResultString.get();
    }
    catch (Exception e) {
      ExceptionLogger.log(e);
      return new Answer.MAYBE("External SMT process failed: " + e.getMessage());
    }
    List<SExpression> parsedResults = SmtParser.readExpressionsFromString(smtResultString);
    Answer ret = SMTLibResponseHandler.expressionsToAnswer(parsedResults);

    // Check if the valuation constructed really makes sense.
    switch (ret) {
      case Answer.YES(Valuation val):
        if (!problem.queryCombinedConstraint().evaluate(val)) {
          return new Answer.MAYBE("Valuation read from external solver " +
            "does not satisfy the constraints posed on the smt problem!");
        }
      default:
        return ret;
    }
  }

  /**
   * Given an SmtProblem, this function tries to prove that it is valid.  This either succeeds, in
   * which case true is returned, or fails, in which case false is returned.
   * <p>
   * Note that failure could either be because the problem is NOT valid, or because the SMT solver
   * simply could not determine whether a solution exists.
   *
   * @param problem
   */
  @Override
  public boolean checkValidity(SmtProblem problem) {

    SMTLibString file = new SMTLibString(V26);
    Constraint negated = SmtFactory.createNegation(problem.queryCombinedConstraint());

    String stringOfSmtProblem =
      file.buildSmtlibString(
        problem.numberBooleanVariables(),
        problem.numberIntegerVariables(),
        problem.numberStringVariables(),
        SMTLibString.getLogic(problem),
        negated
      );

    try {

      Path smtProblemFile = Files.createTempFile("coraSMTTask_validity_", null);
      Files.writeString(smtProblemFile, stringOfSmtProblem);

      ProcessCaller pc = createSmtSolverProcess(smtProblemFile, TIMEOUT);
      Optional<InputStream> is = pc.getResultAsInputStream();

      Files.delete(smtProblemFile);

      if (is.isPresent()) {
        Scanner scanner = new Scanner(is.get());
        return SMTLibResponseHandler.readAnswer(scanner).equals("unsat");
      }
    }
    catch (Exception e) {
      ExceptionLogger.log(e);
      return false; // an error occurred, so no validity could be proven
    }
    return false; // could not read a result, so no validity could be proven
  }
}
