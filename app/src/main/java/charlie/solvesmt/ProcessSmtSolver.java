package charlie.solvesmt;

import charlie.exceptions.NullInitialisationError;
import charlie.smt.*;
import charlie.util.ProcessCaller;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import static charlie.solvesmt.SMTLibString.Logic.QFNIA;
import static charlie.solvesmt.SMTLibString.Version.V26;
import static charlie.solvesmt.ProcessSmtSolver.PhysicalSolver.Z3;

public class ProcessSmtSolver implements SmtSolver {

  public enum PhysicalSolver {
    // Possible solvers supported by the process caller.
    // Note: for security reasons, we cannot allow the user to input any command to be executed as solver.
    // So this list keeps all the possible ones here and only those can be called via the process caller.

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
        case Z3: yield  "z3 -in";
        case CVC5: yield  "cvc";
        case YICES2: yield  "yices-smt2";
      };
    }
  }

  // The default physical solver is z3
  private PhysicalSolver _physicalSolver;

  public ProcessSmtSolver() {
    _physicalSolver = Z3;
  }

  public ProcessSmtSolver(@NotNull PhysicalSolver physicalSolver) {
    if(physicalSolver == null) throw new NullInitialisationError(
      "ProcessSmtSolver",
      "Cannot initialise a null Physical Solver"
    );

    _physicalSolver = physicalSolver;
  }

  private ProcessCaller runSmtSolver(String smtLibString, int timeout) {
    List<String> commands = new ArrayList<>();
    //TODO For now we only care about linux and mac.
    // Proper windows support for the process caller requires this code do identify the
    // current OS the JVM is running on and change the commands accordingly.
    commands.add("/bin/sh");
    commands.add("-c");
    commands.add(STR."echo \" \{smtLibString}\" | \{_physicalSolver.getCommandName()} ");

    return new ProcessCaller(commands, timeout);
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
   *
   * @param problem
   */
  @Override
  public Answer checkSatisfiability(SmtProblem problem) {

    SMTLibString file = new SMTLibString(V26, QFNIA);

    String stringOfSmtProblem = file.buildSmtlibString(problem);

    ProcessCaller pc = runSmtSolver(stringOfSmtProblem, 100);

    String smtResultString = pc.inputStreamToString();

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

    SMTLibString file = new SMTLibString(V26, QFNIA);

    Constraint negated = SmtFactory.createNegation(problem.queryCombinedConstraint());

    String stringOfSmtProblem =
      file.buildSmtlibString(
        problem.numberBooleanVariables(),
        problem.numberIntegerVariables(),
        negated
      );

    ProcessCaller pc = runSmtSolver(stringOfSmtProblem, 100);

    Scanner scanner = new Scanner(pc.getInputStream());

    return SMTLibResponseHandler.readAnswer(scanner).equals("unsat");
  }
}
