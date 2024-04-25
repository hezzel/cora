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
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import charlie.exceptions.ParseError;
import charlie.smt.*;
import org.jetbrains.annotations.NotNull;

/**
 * An ExternalSmtSolver is a solver that operates by writing a file and calling a fixed external
 * SMT solver.  The output file of the solver is read to find the valuation.
 *
 * Note: the idea of calling an external program directly through the "Runtime" caller is outdated
 * and is planned to be phased out in the future.
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
      writer.write(lst.get(i).toSmtString());
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
   * This reads the answer the SMT solver printed to the result file.  It will be either sat,
   * unsat, or a different string which should be expected to correspond to "maybe".  If the file
   * cannot be read ,then null is returned or an IOException thrown, as appropriate.
   */
  private String readAnswer() throws IOException {
    File file = new File("result");
    Scanner reader = new Scanner(file);
    if (!reader.hasNextLine()) return null;
    String answer = reader.nextLine();
    reader.close();
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
    List<SExpression> exprs = SmtParser.readExpressionsFromFile("result");
    if (exprs.size() == 0) return new Answer.MAYBE("SMT solver returned empty expression list");
    switch (exprs.get(0)) {
      case SExpression.Symbol(String answer):
        if (answer.toLowerCase().equals("unsat")) return new Answer.NO();
        if (!answer.toLowerCase().equals("sat")) {
          return new Answer.MAYBE("SMT solver returned: " + answer);
        }
        break;
      default:
        return new Answer.MAYBE("SMT solver returned expression rather than sat/unsat: " +
          exprs.get(0).toString());
    }
    Valuation val = new Valuation();
    for (SExpression e : exprs.subList(1, exprs.size())) addAssignments(e, val);
    return new Answer.YES(val);
  }

  /** Helper function for readSmtFile: finds all assignments in a given answer from an SMT tool. */
  private void addAssignments(SExpression expr, Valuation val) {
    String varname = null;
    SExpression value = null;

    switch (expr) {
      case SExpression.Symbol _:
      case SExpression.Numeral _:
        return; // nothing to do
      case SExpression.SExpList(List<SExpression> lst):
        if (lst.size() == 3 && lst.get(0) instanceof SExpression.Symbol(String symb) &&
            symb.equals("=")) {
          if (lst.get(1) instanceof SExpression.Symbol(String name)) {
            addAssignment(name, lst.get(2), val); return;
          }
          if (lst.get(2) instanceof SExpression.Symbol(String name)) {
            addAssignment(name, lst.get(1), val); return;
          }
        }
        else if (lst.size() == 5 && lst.get(0) instanceof SExpression.Symbol(String symb) &&
                 symb.equals("define-fun") && lst.get(1) instanceof SExpression.Symbol(String n)) {
          addAssignment(n, lst.get(4), val); return;
        }
        else {
          for (SExpression e : lst) addAssignments(e, val);
          return;
        }
    }
  }

  /**
   * Helper function for readSmtFile: adds the given varname ⇒ value pair to the Valuation, if it
   * makes sense to do so.
   */
  private void addAssignment(String varname, SExpression result, Valuation val) {
    if (varname.equals("")) return;
    int kind = 0;
    if (varname.charAt(0) == 'b') kind = 1;
    else if (varname.charAt(0) == 'i') kind = 2;
    else return;
    int index;
    try { index = Integer.parseInt(varname.substring(1)); }
    catch (NumberFormatException e) { return; }

    if (kind == 1) {
      if (result instanceof SExpression.Symbol(String str) && str.equals("true")) {
        val.setBool(index, true);
      }
      else if (result instanceof SExpression.Symbol(String str) && str.equals("false")) {
        val.setBool(index, false);
      }
    }
    else {
      if (result instanceof SExpression.Numeral(int i)) val.setInt(index, i);
      if (result instanceof SExpression.SExpList(List<SExpression> lst)) {
        if (lst.size() == 2 && lst.get(0) instanceof SExpression.Symbol(String name) &&
            name.equals("-") && lst.get(1) instanceof SExpression.Numeral(int k)) {
          val.setInt(index, -k);
        }
      }
    }
  }

  /**
   * Primary access function.  This generates an SMT file from the given SMT problem, executes the
   * SMT solver on it, and reads the result file to obtain a suitable Valuation -- or concludes
   * that no proof can be found.
   */
  public Answer checkSatisfiability(@NotNull SmtProblem problem) {
    Constraint combi = problem.queryCombinedConstraint();
    try {
      createSmtFile(problem.numberBooleanVariables(), problem.numberIntegerVariables(), combi);
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

    Answer ret;
    try { ret = readSmtFile(); }
    catch (IOException e) {
      return new Answer.MAYBE("Error reading result file: " + e.getMessage());
    }
    catch (ParseError e) {
      return new Answer.MAYBE("Parsing error reading result file:\n" + e.getMessage());
    }

    switch (ret) {
      case Answer.YES(Valuation val):
        if (!combi.evaluate(val)) return new Answer.MAYBE("Valuation read from external solver " +
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
