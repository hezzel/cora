/**************************************************************************************************
 Copyright 2019--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.exceptions;

/**
 * An ArityException is thrown when the arity of a type constructor or function symbol is violated,
 * for example by giving it too many or too few arguments.
 */
public class ArityException extends RuntimeException {
  public ArityException(String classname, String functionname, String message) {
    super("Arity exception when calling " + classname + "::" + functionname + ": " + message + ".");
  }
}

