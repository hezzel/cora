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

package cora.io;

import java.util.ArrayList;

/**
 * A TextPageBuilder is a PageBuilder that constructs its output as simple text, using spaces and
 * newlines to create the appropriate structures.
 */
public class TextPageBuilder implements PageBuilder {
  private StringBuilder _builder;

  public TextPageBuilder() {
    _builder = new StringBuilder();
  }

  public void addParagraph(String txt) {
    if (txt.equals("")) _builder.append("\n");
    else {
      _builder.append(txt);
      _builder.append("\n\n");
    }
  }

  public void addTable(Table table) {
    _builder.append(table.toString());
    _builder.append("\n");
  }

  /** Use toString() to get the page as it has been built so far. */
  public String toString() {
    return _builder.toString();
  }
}

