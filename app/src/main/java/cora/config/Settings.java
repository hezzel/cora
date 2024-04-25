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
import charlie.solvesmt.ExternalSmtSolver;
import charlie.solvesmt.ProcessSmtSolver;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;

import java.util.Set;

/**
 * This class collects a number of settings that are global to the execution of Cora or any of its
 * submodules.  The values are meant to be set by the main class (with defaults provided for
 * settings that are not set), and can be queried from any class outside of the cora library.
 */
public class Settings {

  public enum Solver {
    // Possible solvers supported by the process caller.
    // Note: for security reasons, we cannot allow the user to input any command to be executed as solver.
    // So this list keeps all the possible ones here and only those can be called via the process caller.

    Z3, CVC5;

    @Contract(pure = true)
    public @NotNull String getCommandName() {
      return switch (this) {
        case Z3: yield  "z3";
        case CVC5: yield  "cvc";
      };
    }
  }

  private static Settings settingsInstance;

  // Currently chosen solver. This is set on initialization time.
  private Solver _currentSolver;

  public void setSolver(Solver solver) {
    _currentSolver = solver;
  }

  /**
   * Get the command name of the current set solver.
   * If no solver was set, this method sets the solver to Z3 and return the z3 command name.
   * @return
   */
  public String getSolverCommand() {
    if (_currentSolver == null) {
      this.setSolver(Solver.Z3);
    }
    return _currentSolver.getCommandName();
  }

//  public static SmtSolver smtSolver = new ExternalSmtSolver();

  public static SmtSolver smtSolver = new ProcessSmtSolver();

  public static Set<String> disabled = Set.of();

  public static boolean isDisabled(String technique) {
    return disabled.contains(technique);
  }

  private Settings() {}

  /**
   * Lazily Returns the unique instance of this singleton object.
   * If the settings isn't instantiated yet, this method create such instance before returning it.
   * @return
   */
  public static Settings getSettings() {
    if (settingsInstance == null) {
      settingsInstance = new Settings();
    }
    return settingsInstance;
  }

}
