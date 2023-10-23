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
 * A NullCallError is sometimes thrown when a call is given a null argument.
 * This is not meant for constructors or functions which store the given value.  Rather, it is
 * meant to give a clearer message in place of a NullPointerException.  It is not (and does not
 * need to be) consistently used, as it would be bothersome to check for null values in every
 * single function, but may be useful for testing.
 */
public class NullCallError extends Error {
  public NullCallError(String classname, String functionname, String message) {
    super("Calling " + classname + "::" + functionname + " with null argument: " + message + ".");
  }

  public NullCallError(String classname, String functionname) {
    super("Calling " + classname + "::" + functionname + " with a null argument.");
  }
}

