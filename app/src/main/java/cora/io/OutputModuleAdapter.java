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

package cora.io;

import java.util.List;
import cora.exceptions.NullStorageError;
import cora.terms.TermPrinter;

/**
 * An OutputModuleAdapter is used to add functionality to an existing OutputModule.  In particular,
 * it is useful to extend the print() function so as to recognise more options and create special
 * cases for them.
 *
 * To use it, create a new class that inherits OutputModuleAdapter and takes an OutputModule as an
 * argument, and implement the alterObject method.  You can also override other methods, or leave
 * them as they are (to get the functionality from the given OutputModule).
 */
public class OutputModuleAdapter implements OutputModule {
  protected OutputModule _module;

  public OutputModuleAdapter(OutputModule m) {
    if (m == null) throw new NullStorageError("OutputModuleAdapter", "argument module");
    _module = m;
  }

  public Style queryStyle() { return _module.queryStyle(); }
  public TermPrinter queryTermPrinter() { return _module.queryTermPrinter(); }
  public boolean queryInParagraph() { return _module.queryInParagraph(); }
  public void println() { _module.println(); }
  public void startTable() { _module.startTable(); }
  public void nextColumn() { _module.nextColumn(); }
  public void endTable() { _module.endTable(); }
  public void printToStdout() { _module.printToStdout(); }

  public void print(String text, Object ...objects) {
    for (int i = 0; i < objects.length; i++) {
      Object altered = alterObject(objects[i]);
      if (altered != null) objects[i] = altered;
    }
    _module.print(text, objects);
  }

  /**
   * Override this function to implement special support for additional objects.
   *
   * To use it, check if the given object has a type that you want to support.  If not, just return
   * null.  If it does, then return the string you want to print, or a replacement object (for
   * example, a pair (String,Obs) that can the default printer will handle in its own way).
   */
  protected Object alterObject(Object ob) { return null; }
}

