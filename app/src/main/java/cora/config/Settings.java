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
import java.util.Set;

/**
 * This class collects a number of settings that are global to the execution of Cora or any of its
 * submodules.  The values are meant to be set by the main class (with defaults provided for
 * settings that are not set), and can be queried from any class outside of the cora library.
 */
public class Settings {
  public static SmtSolver smtSolver = new ExternalSmtSolver();
  public static Set<String> disabled = Set.of();

  public static boolean isDisabled(String technique) {
    return disabled.contains(technique);
  }
}

