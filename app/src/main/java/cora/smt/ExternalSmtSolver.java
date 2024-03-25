package cora.smt;

import java.io.*;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * An SmtSolver is an object that takes a Constraint and determines its satisfiability.
 * At the moment, we do this by writing a file and calling a fixed external SMT solver, but
 * this may become setting-dependent in the future.
 *
 * NOTE: this is a first draft of the idea.  There is still hacky behaviour in there; the exact
 * workings of the SMT module are yet to be determined, based on what exactly we need.
 */
public class ExternalSmtSolver implements SmtSolver {
 /**
   * This creates a file for the SMT solver.  If creating the file fails for some reason, an
   * IOException is thrown instead.
   */
  private void createSmtFile(int numbool, int numint, Constraint constraint) throws IOException {
    BufferedWriter writer = new BufferedWriter(new FileWriter("problem.smt2"));
    writer.write("(set-info :smt-lib-version 2.6)"); writer.newLine();
    writer.write("(set-logic QF_NIA)"); writer.newLine();
    for (int i = 1; i <= numbool; i++) {
      writer.write("(declare-fun b" + i + "() Bool)"); writer.newLine();
    }
    for (int i = 1; i <= numint; i++) {
      writer.write("(declare-fun i" + i + "() Int)"); writer.newLine();
    }
    ArrayList<Constraint> lst = new ArrayList<Constraint>();
    if (constraint instanceof Conjunction) {
      Conjunction c = (Conjunction)constraint;
      for (int i = 1; i <= c.numChildren(); i++) lst.add(c.queryChild(i));
    }
    else lst.add(constraint);
    for (int i = 0; i < lst.size(); i++) {
      writer.write("(assert ");
      writer.write(lst.get(i).toString());
      writer.write(")");
      writer.newLine();
    }
    writer.write("(check-sat)"); writer.newLine();
    writer.write("(get-model)"); writer.newLine();
    writer.write("(exit)");      writer.newLine();
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
   * This extends the given valuation by the next model assignment in the SMT output file that is
   * read by reader.  Returns null if everything went well, and a failure message if not.
   *
   * We expect one of the following formats:
   * - (= varname value)
   * - (define-fun varname () type value)
   */
  private String addModelAssignment(Valuation val, Scanner reader) {
    String style = reader.next();
    if (!style.equals("=") && !style.equals("define-fun")) {
      return "Unexpected token in result file: " + style;
    }
    if (!reader.hasNext()) return "Result file ended unexpectedly after " + style;
    String varname = reader.next();
    int kind = 0;
    if (varname.substring(0,1).equals("b")) kind = 1;
    else if (varname.substring(0,1).equals("i")) kind = 2;
    if (kind == 0) return "Unexpected variable: " + varname + ".";
    int index;
    try { index = Integer.parseInt(varname.substring(1)); }
    catch (NumberFormatException e) { return "Unexpected variable: " + varname + "."; }
    if (!reader.hasNext()) return "Result file ended unexpectedly after " + varname + ".";

    if (style.equals("define-fun")) reader.next();  // skip over the type

    int multiplier = 1;
    String value = reader.next();
    if (value.equals("-")) { multiplier *= -1; value = reader.next(); }
    if (kind == 1) {
      if (value.equals("true")) val.setBool(index, true);
      else if (value.equals("false")) val.setBool(index, false);
      else return "Unexpected value for boolean variable " + varname + ": " + value + ".";
    }
    else {
      try { int v = Integer.parseInt(value); val.setInt(index, multiplier * v); }
      catch (NumberFormatException e) {
        return "Unexpected value for integer variable " + varname + ": " + value + ".";
      }
    }
    return null;
  }

  /**
   * This reads the answer the SMT solver printed to the result file.  It will be either sat,
   * unsat, or a different string which should be expected to correspond to "maybe".  If the file
   * cannot be read ,then null is returned or an IOException thrown, as appropriate.
   */
  private String readAnswer() throws IOException {
    File file = new File("result");
    Scanner reader = new Scanner(file);
    if (!reader.hasNextLine()) return null;
    String answer = reader.nextLine();
    if (answer.toLowerCase().equals("unsat")) return "unsat";
    if (!answer.toLowerCase().equals("sat")) return "sat";
    return answer;
  }

  /**
   * This reads the solution from the expected SMT output file, and returns the corresponding
   * Answer.
   * If the file cannot be read -- for example because the SMT solver failed -- then MAYBE is
   * returned (with an appropriate failure meesage).  The same holds if satisfiability could not
   * be determined.  If the result is not satisfiable, then NO is returned.
   */
  private Answer readSmtFile() throws IOException {
    File file = new File("result");
    Scanner reader = new Scanner(file);
    if (!reader.hasNextLine()) return new Answer.MAYBE("Could not read result file.");
    String answer = reader.nextLine();
    if (answer.toLowerCase().equals("unsat")) return new Answer.NO();
    if (!answer.toLowerCase().equals("sat")) {
      return new Answer.MAYBE("SMT solver returned: " + answer);
    }
    reader.useDelimiter("[\\s()]+");
    Valuation val = new Valuation();
    while (reader.hasNext()) {
      String warning = addModelAssignment(val, reader);
      if (warning != null) return new Answer.MAYBE(warning);
    }
    return new Answer.YES(val);
  }

  /**
   * Primary access function.  This generates an SMT file from the given SMT problem, executes the
   * SMT solver on it, and reads the result file to obtain a suitable Valuation -- or concludes
   * that no proof can be found.
   */
  public Answer checkSatisfiability(SmtProblem problem) {
    try {
      createSmtFile(problem.numberBooleanVariables(), problem.numberIntegerVariables(),
                    problem.queryCombinedConstraint());
    }
    catch (IOException e) {
      return new Answer.MAYBE("Could not create SMT file: " + e.getMessage());
    }

    try { runSmtSolver(); }
    catch (IOException e) {
      return new Answer.MAYBE("Could not execute SMT solver: " + e.getMessage());
    }
    catch (InterruptedException e) {
      return new Answer.MAYBE("Waiting for external SMT solver was interrupted: " + e.getMessage()
                              + "\n(Warning: the SMT solver may still be running in the " +
                              "background.  If so, you may need to kill it.\n");
    }

    try { return readSmtFile(); }
    catch (IOException e) {
      return new Answer.MAYBE("Error reading result file: " + e.getMessage());
    }
  }

  /**
   * Convenience function.  This uses checkSatiability on the negation of the constraint obtained
   * from checkSatisfiability to determine if the conjunction of the formulas in SmtProblem is
   * valid.
   */
  public boolean checkValidity(SmtProblem problem) {
    Constraint negated = new Not(problem.queryCombinedConstraint());
    try {
      createSmtFile(problem.numberBooleanVariables(), problem.numberIntegerVariables(), negated);
      runSmtSolver();
      return readAnswer().equals("unsat");
    }
    catch (Exception e) { return false; } // we could not conclude validity
  }
}

