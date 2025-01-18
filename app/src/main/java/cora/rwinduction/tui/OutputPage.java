/**************************************************************************************************
 Copyright 2025 Cynthia Kop

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

import cora.io.PageBuilder;

/**
 * The OutputPage is a PageBuilder that prints directly to the user's terminal.  When used as part
 * of an OutputModule, this offers a convenient way to print output to the user.
 */
public class OutputPage implements PageBuilder {
  public void addParagraph(String txt) {
    System.out.println(txt + "\n");
  }

  public void addTable(Table table) {
    System.out.println(table.toString() + "\n");
  }
}

