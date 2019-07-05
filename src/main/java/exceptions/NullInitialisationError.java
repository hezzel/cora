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
 * A NullInitialisationError is thrown when we try to construct an object but one of its arguments
 * is null (that should not be).
 * For calls other than constructors, use a NullStorageError instead if (parts of) the value would
 * end up being stored in the object., or NullCallError if the null value simply ends up being used
 * and you want to throw a different Error (with clearer message) than a NullPointerException.
 */
public class NullInitialisationError extends Error {
  public NullInitialisationError(String classname, String message) {
    super("Trying to initialise " + classname + " with a null argument: " + message + ".");
  }
}

