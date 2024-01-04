package cora.smt;

import java.io.*;
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
class SmtSolver {
 /**
   * This creates a file for the SMT solver and returns true, or prints a message to stderr and
   * throws an Error if creating the file fails for some reason.
   */
  private static boolean createSmtFile(TreeSet<Integer> boolVars, TreeSet<Integer> intVars,
                                       Constraint constraint) {
    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter("problem.smt2"));
      writer.write("(set-info :smt-lib-version 2.6)"); writer.newLine();
      writer.write("(set-logic QF_NIA)"); writer.newLine();
      for (Integer x : boolVars) {
        writer.write("(declare-fun b" + x.toString() + "() Bool)"); writer.newLine();
      }
      for (Integer y : intVars) {
        writer.write("(declare-fun i" + y.toString() + "() Int)"); writer.newLine();
      }
      writer.write("(assert ");
      writer.write(constraint.toString());
      writer.write(")");
      writer.newLine();
      writer.write("(check-sat)"); writer.newLine();
      writer.write("(get-model)"); writer.newLine();
      writer.write("(exit)");      writer.newLine();
      writer.close();
    } catch (IOException e) {
      System.err.println("Could not create SMT file.");
      e.printStackTrace();
      return false;
    }
    return true;
  }

  /**
   * This function runs the SMT solver on problem.smt2 and returns true if it succeeded; it it did
   * not, a message is printed instead.
   */
  private static boolean runSmtSolver() {
    Runtime rt = Runtime.getRuntime();
    // clean up old result, it any
    try { Process p = rt.exec("rm result"); p.waitFor(); } catch (Exception e) {}
    // start new satsolver process
    try {
      Process p = rt.exec("./smtsolver problem.smt2 result");
      p.waitFor();
    } catch (Exception e) {
      System.err.println("Could not execute smtsolver.");
      e.printStackTrace();
      return false;
    }
    return true;
  }

  /**
   * This extends the given solution by the next model assignment in the SMT output file that is
   * read by reader.  Returns null if everything went well, and a failure message if not.
   *
   * We expect one of the following formats:
   * - (= varname value)
   * - (define-fun varname () type value)
   */
  private static String addModelAssignment(Valuation val, Scanner reader) {
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
   * unsat, or maybe. (If the result file does not contain one of those options as the first line,
   * or cannot be read, then maybe will be returned.)
   */
  private static String readAnswer() {
    try {
      File file = new File("result");
      Scanner reader = new Scanner(file);
      if (!reader.hasNextLine()) {
        System.err.println("Could not read result file.");
        return null;
      }
      String answer = reader.nextLine();
      if (answer.toLowerCase().equals("unsat")) return "unsat";
      if (!answer.toLowerCase().equals("sat")) return "sat";
      return "maybe";
    } catch (IOException e) {
      return "maybe";
    }
  }

  /**
   * This reads the solution from the expected SMT output file, and turns it into a Valuation.
   * If the file cannot be read -- for example because the SMT solver failed -- then null is
   * returned instead (and a message printed to stderr).
   * If the result is not satisfiable, or satisfiability cannot be determined, then null is also
   * returned.
   */
  private static Valuation readSmtFile() {
    try {
      File file = new File("result");
      Scanner reader = new Scanner(file);
      if (!reader.hasNextLine()) {
        System.err.println("Could not read result file.");
        return null;
      }
      String answer = reader.nextLine();
      if (answer.toLowerCase().equals("unsat")) return null;
      if (!answer.toLowerCase().equals("sat")) {
        System.err.println("Unexpected answer: " + answer);
        return null;
      }
      reader.useDelimiter("[\\s()]+");
      Valuation val = new Valuation();
      while (reader.hasNext()) {
        String warning = addModelAssignment(val, reader);
        if (warning != null) {
          System.err.println(warning);
          return null;
        }
      }
      return val;
    } catch (IOException e) {
      System.err.println("Error reading result file.");
      e.printStackTrace();
      return null;
    }
  }

  /**
   * This yields a valuation that satisfies the given constraint, by invoking an external SMT
   * solver, or returns null if the external SMT solver could not find a solution.
   */
  public static Valuation checkSatisfiability(TreeSet<Integer> boolVars, TreeSet<Integer> intVars,
                                              Constraint constraint) {
    if (!createSmtFile(boolVars, intVars, constraint)) return null;
    if (!runSmtSolver()) return null;
    return readSmtFile();
  }

  /**
   * This function checks whether a given constraint is definitely valid (that is, its negation is
   * unsatisfiable).  This is done by writing the negated formula to a file, and calling yices; if
   * yices returns NO (so the negation is unsatisfiable), this returns true; if it returns either
   * YES or MAYBE, it returns false. (So false negatives are possible for challenging constraints).
   */
  public static boolean checkValidity(TreeSet<Integer> boolVars, TreeSet<Integer> intVars,
                                      Constraint constraint) {
    Constraint negated = new Not(constraint);
    if (!createSmtFile(boolVars, intVars, negated)) return false;
    if (!runSmtSolver()) return false;
    return readAnswer().equals("unsat");
  }
}
