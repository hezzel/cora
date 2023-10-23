/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.exceptions;

/**
 * A TypingError is thrown when the typing of some term fails, for example because something tries
 * to assign a non-integer type to an integer value, or when a function of type A -> B -> C is
 * applied on two arguments of type A.
 */
public class TypingError extends Error {
  public TypingError(String classname, String functionname, String what, String given,
                     String expected) {
    super("Type error when calling " + classname + "::" + functionname + ": " + what + " should " +
      "have type " + expected + " but has type " + given + ".");
  }
}

