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

package cora.rwinduction.tui;

import java.util.ArrayList;

import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Renaming;
import cora.io.OutputModule;
import cora.io.OutputModuleAdapter;
import cora.rwinduction.engine.EquationPosition;
import cora.rwinduction.engine.Equation;

/**
 * The Outputter is an OutputModule specifically for use in the interactive rewriting induction
 * module.  Aside from the usual functionality (plus the ability to print equations using the %a
 * syntax), this class offers a flush() method that immediately prints the collected information to
 * the user.
 */
public class Outputter extends OutputModuleAdapter {
  public Outputter(OutputModule m) {
    super(m);
  }

  protected Object alterObject(Object ob) {
    if (ob instanceof Equation eq) return alterEquation(eq);
    if (ob instanceof EquationPosition ep) return alterPosition(ep);
    return null;
  }

  protected Object alterEquation(Equation eq) {
    String ret = "%a %{approx} %a";
    ArrayList<Object> args = new ArrayList<Object>(4);
    Renaming naming = eq.getRenaming();
    Term constraint = eq.getConstraint();
    args.add(new Pair<Term,Renaming>(eq.getLhs(), naming));
    args.add(new Pair<Term,Renaming>(eq.getRhs(), naming));
    if (!constraint.isValue() || !constraint.toValue().getBool()) {
      ret += " | %a";
      args.add(new Pair<Term,Renaming>(constraint, naming));
    }
    return new Pair<String,Object[]>(ret, args.toArray());
  }

  protected Object alterPosition(EquationPosition pos) {
    String side = pos.querySide() == EquationPosition.Side.Left ? "L" : "R";
    if (pos.queryPosition().isEmpty()) return side;
    return new Pair<String,Object[]>("%a.%a", new Object[] { side, pos.queryPosition() });
  }

  /**
   * This function prints the collected information from the output module to the user.  After the
   * flush, the module is cleared, so the information will not be printed again on the next flush.
   */
  public void flush() {
    _module.printToStdout();
    _module.clear();
  }
}

