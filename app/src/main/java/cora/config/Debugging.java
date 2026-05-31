/**************************************************************************************************
 Copyright 2026 Cynthia Kop

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

import charlie.util.ExceptionLogger;
import charlie.types.TypePrinter;

/**
 * This class allows Cora to easily access debugging settings, such as the way things are printed
 * by default, or how certain exceptions are handled.
 */
public class Debugging {
  /**
   * If this is called, any exception that is logged rather than thrown outright will be hidden.
   * By default (if this is not called), such exceptions are printed on stderr instead.
   */
  public static void setHideExceptionLogging() {
    ExceptionLogger.disable();
  }

  /**
   * By default, the toString() function in terms and types will often include unicode symbols.
   * If you call this function, this will be changed to avoid unicode where possible.
   */
  public static void disableUnicode() {
    TypePrinter.disableDefaultUnicode();
  }
}
