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

import charlie.smt.Conjunction;
import charlie.smt.Constraint;
import charlie.smt.SmtProblem;

import java.util.ArrayList;

/**
 * <p>This class helps with the construction of a smtlib2-compliant representation of an
 * {@link SmtProblem} object.</p>
 * <p>The main method to be called is {@link #buildSmtlibString }. </p>
 */
class SMTLibString {
  public enum Version { V25   , V26   }
  public enum Logic   { QFLIA , QFNIA , QFSNIA }

  private Version _version;
  private Logic _logic;

  public SMTLibString(Version version) {
    _version = version;
  }

  public Version getVersion() { return _version; }

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
      case QFSNIA -> "QF_SNIA";
    };
  }

  /**
   * This returns a logic suitable for the given problem.
   * Note that this may be an overestimate; for example, using non-linear arithmetic where linear
   * arithmetic would suffice.
   */
  public static Logic getLogic(SmtProblem problem) {
    if (problem.numberStringVariables() > 0) return Logic.QFSNIA;
    else return Logic.QFNIA;
  }

  private String setVersionString() {
    return "(set-info :smt-lib-version " + SMTLibString.versionToString(this.getVersion()) + ")";
  }

  private String setLogicString(Logic logic) {
    return "(set-logic " + SMTLibString.logicToString(logic) + ")";
  }

  /**
   * Returns the SMTLIB string representation of the problem given as input.
   * @param {@link SmtProblem} problem
   */
  public String buildSmtlibString(int boolCounter, int intCounter, int stringCounter,
                                  Logic logic, Constraint constraint) {
    StringBuilder ret = new StringBuilder();

    // Create the SMTLIB file header.
    ret.append(this.setVersionString()).append(System.lineSeparator());
    ret.append(this.setLogicString(logic)).append(System.lineSeparator());

    // Next, we collect all booleans and integer definitions.
    for (int i = 1; i <= boolCounter; i++) {
      ret.append("(declare-fun b").append(i).append("() Bool)").append(System.lineSeparator());
    }
    for (int i = 1; i <= intCounter; i++) {
      ret.append("(declare-fun i").append(i).append("() Int)").append(System.lineSeparator());
    }
    for (int i = 1; i <= stringCounter; i++) {
      ret.append("(declare-fun s").append(i).append("() String)").append(System.lineSeparator());
    }

    // Split up the constraints into separate clauses for human-readability (in case this is
    // useful).
    ArrayList<Constraint> acc = new ArrayList<>();
    if (constraint instanceof Conjunction c) {
      for (int i = 1; i <= c.numChildren(); i++) acc.add(c.queryChild(i));
    } else {
      acc.add(constraint);
    }

    // Add to the file string the assertions of each one of those constraints
    for (Constraint c : acc) {
      ret.append("(assert ");
      c.addToSmtString(ret);
      ret.append(")").append(System.lineSeparator());
    }

    // Check for satisfiability and asks for the file model
    ret.append("(check-sat)").append(System.lineSeparator());
    ret.append("(get-model)").append(System.lineSeparator());
    ret.append("(exit)").append(System.lineSeparator());

    return ret.toString();
  }

  public String buildSmtlibString(SmtProblem problem) {
    return buildSmtlibString(
      problem.numberBooleanVariables(),
      problem.numberIntegerVariables(),
      problem.numberStringVariables(),
      getLogic(problem),
      problem.queryCombinedConstraint()
    );
  }
}
