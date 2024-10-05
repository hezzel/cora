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

package cora.config;

import charlie.smt.SmtSolver;
import charlie.solvesmt.ProcessSmtSolver;
import java.util.Set;

/**
 * This class collects a number of settings that are global to the execution of Cora or any of its
 * submodules.  The values are meant to be set by the main class (with defaults provided for
 * settings that are not set), and can be queried from any class outside of the cora library.
 */
public class Settings {
  public enum Strategy { Full , Innermost , CallByValue };
  private static Set<String> _disabled = Set.of();
  private static Strategy _strategy = Strategy.Full;

  /** The SMT solver that any SMT-encoding submodule should use. */
  public static SmtSolver smtSolver = new ProcessSmtSolver(ProcessSmtSolver.PhysicalSolver.Z3);

  /** Use this to check if a technique is diabled (by name). */
  public static boolean isDisabled(String technique) {
    return _disabled.contains(technique);
  }

  /** Use this to check the rewriting strategy the user wishes to consider by default. */
  public static Strategy queryRewritingStrategy() {
    return _strategy;
  }

  /** Used to set up the SMT solver. */
  public static void setSolver(SmtSolver solver) {
    smtSolver = solver;
  }

  /** Used to set up which techniques are disabled. */
  public static void setDisabled(Set<String> disabledTechniques) {
    _disabled = disabledTechniques;
  }

  /** Used to set up the strategy. */
  public static void setStrategy(Strategy strat) {
    _strategy = strat;
  }
}
