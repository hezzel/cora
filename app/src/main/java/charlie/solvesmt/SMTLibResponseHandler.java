package charlie.solvesmt;

import charlie.smt.*;
import java.util.List;
import java.util.Scanner;

public class SMTLibResponseHandler {

  /**
   * This reads the answer the SMT solver printed to the result file.  It will be either sat,
   * unsat, or a different string which should be expected to correspond to "maybe".  If the file
   * cannot be read ,then null is returned or an IOException thrown, as appropriate.
   */
  static String readAnswer(Scanner reader) {
    if (!reader.hasNextLine()) return null;
    String answer = reader.nextLine();
    reader.close();
    if (answer.toLowerCase().equals("unsat")) return "unsat";
    if (!answer.toLowerCase().equals("sat")) return "sat";
    return answer;
  }

  static SmtSolver.Answer expressionsToAnswer(List<SExpression> exprs) {
    if (exprs.size() == 0) return new SmtSolver.Answer.MAYBE("SMT solver returned empty expression list");
    switch (exprs.get(0)) {
      case SExpression.Symbol(String answer):
        if (answer.toLowerCase().equals("unsat")) return new SmtSolver.Answer.NO();
        if (!answer.toLowerCase().equals("sat")) {
          return new SmtSolver.Answer.MAYBE(STR."SMT solver returned: \{answer}");
        }
        break;
      default:
        return new
          SmtSolver.
            Answer.
            MAYBE(STR."SMT solver returned expression rather than sat/unsat: \{exprs.get(0).toString()}");
    }
    Valuation val = new Valuation();
    for (SExpression e : exprs.subList(1, exprs.size())) addAssignments(e, val);
    return new SmtSolver.Answer.YES(val);
  }

  /** Helper function: finds all assignments in a list of SExpressions. */
  private static void addAssignments(SExpression expr, Valuation val) {
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
        }
    }
  }

  /**
   * Helper function: adds the given varname ⇒ value pair to the given Valuation,
   * if it makes sense to do so.
   */
  private static void addAssignment(String varname, SExpression result, Valuation val) {
    if (varname.isEmpty()) return;
    int kind;
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

}
