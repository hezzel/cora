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

/**
 * The rewriting induction module needs to receive input from some source.  Input could for
 * instance be equations, or commands.  It could be obtained just by reading input directly,
 * by reading from a file, or some kind of graphical interface.
 */
public interface Inputter {
  /** Reads a single line from input. */
  default String readLine() {
    return readLine("> ");
  }

  /**
   * Prints the given string to the user, then reads a single line from input.  If the input is
   * already available -- for example because it is cached, or we are reading from a file -- then
   * the text might not be printed.
   */
  String readLine(String prompt);

  /** Closes the inputter (always called at the end of the interactive process). */
  void close();
}
