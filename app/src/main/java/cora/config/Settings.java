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
import charlie.solvesmt.ProcessSmtSolver.*;
import java.util.Set;

/**
 * This class collects a number of settings that are global to the execution of Cora or any of its
 * submodules.  The values are meant to be set by the main class (with defaults provided for
 * settings that are not set), and can be queried from any class outside of the cora library.
 */
public class Settings {

  // Sets cora to use the external smt solver.
  // This one writes the smtstring as a file on disk and reads the result back from it.
  // It requires auxiliary files in order to run cora on it.
  // Before using this solver, please make sure such script is present on disk.
  // public static SmtSolver smtSolver = new ExternalSmtSolver();

  private static PhysicalSolver physicalSolver =
    PhysicalSolver.Z3;

  public static SmtSolver smtSolver =
    new ProcessSmtSolver(physicalSolver);

  public static Set<String> disabled = Set.of();

  public static boolean isDisabled(String technique) {
    return disabled.contains(technique);
  }

  private static Settings settingsInstance;

  private Settings() {}

  /**
   * Lazily Returns the unique instance of this singleton object.
   * If the settings isn't instantiated yet,
   * this method create such instance before returning it.
   * Up to now the default settings is:
   * SmtSolver to be used: ProcessSolver
   * PhysicalSolver to be used: Z3.
   * @return
   */
  public static Settings getSettingsInstance() {
    if (settingsInstance == null) {
      settingsInstance = new Settings();
    }
    return settingsInstance;
  }

  public static void setPhysicalSolver(PhysicalSolver physicalSolver) {
    Settings.physicalSolver = physicalSolver;
  }

}
