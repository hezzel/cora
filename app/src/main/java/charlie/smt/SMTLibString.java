package charlie.smt;

import java.util.ArrayList;

public class SMTLibString {

  public enum Version { V25   , V26   }
  public enum Logic   { QFLIA , QFNIA }

  private Version _version;
  private Logic _logic;

  public SMTLibString(Version version, Logic logic) {
    _version = version;
    _logic = logic;
  }

  public Version getVersion() { return _version; }

  public Logic getLogic() {return _logic; }

  public static String versionToString(Version version) {
    return switch (version) {
      case V25 -> "2.5";
      case V26 -> "2.6";
    };
  }

  public static String logicToString(Logic logic) {
    return switch (logic) {
      case QFLIA -> "QF_LIA";
      case QFNIA -> "QF_NIA";
    };
  }

  private String setVersionString() {
    return STR."(set-info :smt-lib-version \{SMTLibString.versionToString(this.getVersion())})";
  }

  private String setLogicString() {
    return STR."(set-logic \{SMTLibString.logicToString(this.getLogic())})";
  }

  public String buildSmtlibString(SmtProblem problem) {
    int boolsCounter = problem.numberBooleanVariables();
    int intCounter = problem.numberIntegerVariables();
    StringBuilder ret = new StringBuilder();

    // Create the SMTLIB file header.
    ret.append(this.setVersionString()).append(System.lineSeparator());
    ret.append(this.setLogicString()).append(System.lineSeparator());

    // Next, we collect all booleans and integer definitions.
    // Booleans
    for (int i = 1; i <= boolsCounter; i++) {
      ret.append("(declare-fun b").append(i).append("() Bool)").append(System.lineSeparator());
    }

    // Integers
    for (int i = 1; i <= intCounter; i++) {
      ret.append("(declare-fun i").append(i).append("() Int)").append(System.lineSeparator());
    }

    // Split the conjunctions into individual constraints and put them
    // in an accumulator list
    Constraint constraint = problem.queryCombinedConstraint();
    ArrayList<Constraint> acc = new ArrayList<>();
    if (constraint instanceof Conjunction) {
      Conjunction c = (Conjunction) constraint;
      for (int i = 1; i <= c.numChildren(); i++) acc.add(c.queryChild(i));
    } else {
      acc.add(constraint);
    }

    // Add to the file string the assertions of each one of those constraints
    for (Constraint c : acc) {
      ret.append("(assert ").append(c.toString()).append(")").append(System.lineSeparator());
    }

    // Check for satisfiability and asks for the file model
    ret.append("(check-sat)").append(System.lineSeparator());
    ret.append("(get-model)").append(System.lineSeparator());
    ret.append("(exit)").append(System.lineSeparator());

    return ret.toString();
  }

}
