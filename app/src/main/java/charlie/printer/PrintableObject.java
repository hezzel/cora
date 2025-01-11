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

package charlie.printer;

/**
 * A PrintableObject is an object that knows how to print itself to a given Printer.  Thus, any
 * PrintableObject can be used as one of the arguments to Printer::add.
 */
public interface PrintableObject {
  /**
   * When given a PrintableObject, the Printer will invoke this function (with itself as argument)
   * to add a representation of the current object to the printer.
   */
  void print(Printer printer);
}

