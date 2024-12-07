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

import java.util.Scanner;

/** The BasicInputter just reads from stdin without any sophistication. */
public class BasicInputter implements Inputter {
  Scanner _scanner;

  public BasicInputter() {
    _scanner = new Scanner(System.in);
  }

  /** Prints the given string to the user, then reads a single line from input. */
  public String readLine(String prompt) {
    System.out.print(prompt);
    return _scanner.nextLine();
  }

  /** Does nothing */
  public void close() { }
}
